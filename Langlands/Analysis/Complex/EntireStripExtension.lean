import Langlands.LocalFactor.Archimedean.GammaStripGrowth
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.PhragmenLindelof

/-! # Limits of entire functions controlled on pairs of vertical lines -/

noncomputable section

open Filter Set
open scoped Topology
open Langlands.LocalFactor.Archimedean (HasStripExponentialGrowth)

set_option autoImplicit false

namespace Langlands.Analysis

private theorem re_sq_le {a b : ℝ} {z : ℂ} (ha : a ≤ z.re) (hb : z.re ≤ b) :
    z.re ^ 2 ≤ (max |a| |b|) ^ 2 := by
  have h := abs_le.mpr
    ⟨(neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans ha),
      hb.trans ((le_abs_self b).trans (le_max_right |a| |b|))⟩
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z.re) h 2

private theorem linear_sub_quadratic_le {ε : ℝ} (hε : 0 < ε) (K y : ℝ) :
    K * |y| - ε * y ^ 2 ≤ K ^ 2 / (4 * ε) := by
  apply (le_div_iff₀ (by positivity)).mpr
  rw [← sq_abs y]
  nlinarith [sq_nonneg (2 * ε * |y| - K)]

private theorem norm_gaussianDamp (ε : ℝ) (z : ℂ) :
    ‖Complex.exp ((ε : ℂ) * z ^ 2)‖ = Real.exp (ε * (z.re ^ 2 - z.im ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- A common exponential estimate on the two boundary lines gives an exponential
estimate inside the strip. The interior constant depends only on the boundary
estimate and the real coordinates of the boundary lines. -/
theorem norm_le_of_exp_bounds_on_vertical_lines {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : HasStripExponentialGrowth f) {a b C K : ℝ} (hab : a < b) (hC : 0 ≤ C)
    (hline : ∀ w : ℂ, w.re = a ∨ w.re = b → ‖f w‖ ≤ C * Real.exp (K * |w.im|))
    {z : ℂ} (ha : a ≤ z.re) (hb : z.re ≤ b) :
    ‖f z‖ ≤ C * Real.exp ((max |a| |b|) ^ 2 + K ^ 2 / 4 + (1 + K ^ 2 / 4) * |z.im|) := by
  let P := (max |a| |b|) ^ 2
  let x := |z.im|
  let ε := 1 / (1 + x)
  have hden : 0 < 1 + x := by dsimp [x]; positivity
  have hε : 0 < ε := one_div_pos.mpr hden
  have hε₁ : ε ≤ 1 := (div_le_one hden).mpr (le_add_of_nonneg_right (abs_nonneg z.im))
  let g (w : ℂ) := f w * Complex.exp ((ε : ℂ) * w ^ 2)
  have hgd : Differentiable ℂ g :=
    hf.mul (((differentiable_id.pow 2).const_mul (ε : ℂ)).cexp)
  have hbound {D L : ℝ} (hD : 0 ≤ D) {w : ℂ} (hla : a ≤ w.re) (hlb : w.re ≤ b)
      (hw : ‖f w‖ ≤ D * Real.exp (L * |w.im|)) :
      ‖g w‖ ≤ D * Real.exp (ε * P + L ^ 2 / (4 * ε)) := by
    change ‖f w * Complex.exp ((ε : ℂ) * w ^ 2)‖ ≤ _
    rw [norm_mul, norm_gaussianDamp]
    calc
      _ ≤ (D * Real.exp (L * |w.im|)) * Real.exp (ε * (w.re ^ 2 - w.im ^ 2)) :=
        mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
      _ = D * Real.exp (L * |w.im| + ε * (w.re ^ 2 - w.im ^ 2)) := by
        rw [Real.exp_add, mul_assoc]
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD
        linarith [mul_le_mul_of_nonneg_left (re_sq_le hla hlb) hε.le,
          linear_sub_quadratic_le hε L w.im]
  obtain ⟨D, L, T, hD, _, hGrowth⟩ := hg a b
  have hStrip := PhragmenLindelof.vertical_strip (a := a) (b := b) (f := g)
     (z := z) (C := C * Real.exp (ε * P + K ^ 2 / (4 * ε))) hgd.diffContOnCl
  have hgrowth :
      ∃ c < Real.pi / (b - a), ∃ B : ℝ, g =O[comap (abs ∘ Complex.im) atTop ⊓
        𝓟 (Complex.re ⁻¹' Ioo a b)] fun w => Real.exp (B * Real.exp (c * |w.im|)) := by
    refine ⟨0, div_pos Real.pi_pos (sub_pos.mpr hab), 0, Asymptotics.IsBigO.of_bound
      (D * Real.exp (ε * P + L ^ 2 / (4 * ε))) ?_⟩
    have hT : ∀ᶠ w : ℂ in comap (abs ∘ Complex.im) atTop, T ≤ |w.im| := by
      apply eventually_comap.2
      filter_upwards [eventually_ge_atTop T] with t ht w hw
      change |w.im| = t at hw
      rwa [hw]
    filter_upwards [hT.filter_mono inf_le_left, (eventually_mem_principal
      (Complex.re ⁻¹' Ioo a b)).filter_mono inf_le_right] with w ht hw
    simpa only [zero_mul, Real.exp_zero, norm_one, mul_one] using
      hbound hD hw.1.le hw.2.le (hGrowth w hw.1.le hw.2.le ht)
  have hgz := hStrip hgrowth
    (fun w hw => hbound hC hw.ge (hw.trans_le hab.le) (hline w (Or.inl hw)))
    (fun w hw => hbound hC (hab.le.trans hw.ge) hw.le (hline w (Or.inr hw))) ha hb
  change ‖f z * Complex.exp ((ε : ℂ) * z ^ 2)‖ ≤ _ at hgz
  rw [norm_mul, norm_gaussianDamp] at hgz
  calc
    ‖f z‖ ≤ (C * Real.exp (ε * P + K ^ 2 / (4 * ε))) /
        Real.exp (ε * (z.re ^ 2 - z.im ^ 2)) := (le_div_iff₀ (Real.exp_pos _)).mpr hgz
    _ = C * Real.exp (ε * P + K ^ 2 / (4 * ε) - ε * (z.re ^ 2 - z.im ^ 2)) := by
      rw [mul_div_assoc, ← Real.exp_sub]
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
      have h₁ : ε * P ≤ P := mul_le_of_le_one_left (sq_nonneg _) hε₁
      have h₂ : ε * z.im ^ 2 ≤ x := by
        rw [← sq_abs z.im]
        change (1 / (1 + x)) * x ^ 2 ≤ x
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hden]
        nlinarith [abs_nonneg z.im]
      have h₃ : K ^ 2 / (4 * ε) = (K ^ 2 / 4) * (1 + x) := by
        dsimp only [ε]
        field_simp [hden.ne']
      rw [h₃]
      nlinarith [mul_nonneg hε.le (sq_nonneg z.re)]

private theorem stripGrowth_sub {f g : ℂ → ℂ} (hf : HasStripExponentialGrowth f)
    (hg : HasStripExponentialGrowth g) : HasStripExponentialGrowth (f - g) := by
  intro a b
  obtain ⟨C, K, T, hC, hK, hF⟩ := hf a b
  obtain ⟨D, L, U, hD, hL, hG⟩ := hg a b
  refine ⟨C + D, max K L, max T U, add_nonneg hC hD, hK.trans (le_max_left _ _), ?_⟩
  intro z ha hb hz
  rw [add_mul]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · refine (hF z ha hb ((le_max_left _ _).trans hz)).trans ?_
    gcongr
    exact le_max_left _ _
  · refine (hG z ha hb ((le_max_right _ _).trans hz)).trans ?_
    gcongr
    exact le_max_right _ _

/-- Exponentially weighted Cauchy estimates on arbitrarily distant pairs of
vertical lines give an entire locally uniform limit with exponential strip growth. -/
def EntireStripExtensionStatement : Prop :=
  ∀ (F : ℕ → ℂ → ℂ), (∀ n, Differentiable ℂ (F n)) →
    (∀ n, HasStripExponentialGrowth (F n)) →
    (∀ u v : ℝ, u ≤ v → ∃ a b K : ℝ, a < u ∧ v < b ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        ∀ z : ℂ, z.re = a ∨ z.re = b → ‖F n z - F m z‖ ≤ ε * Real.exp (K * |z.im|)) →
    ∃ f : ℂ → ℂ, TendstoLocallyUniformly F f atTop ∧ Differentiable ℂ f ∧ HasStripExponentialGrowth f

theorem entireStripExtension : EntireStripExtensionStatement := by
  intro F hF hG hlines
  have hstrips (u v : ℝ) (huv : u ≤ v) :
      ∃ A B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        ∀ z : ℂ, u ≤ z.re → z.re ≤ v → ‖F n z - F m z‖ ≤ ε * Real.exp (A + B * |z.im|) := by
    obtain ⟨a, b, K, ha, hb, h⟩ := hlines u v huv
    refine ⟨(max |a| |b|) ^ 2 + K ^ 2 / 4, 1 + K ^ 2 / 4, by positivity, ?_⟩
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n m hn hm z hz hz' => norm_le_of_exp_bounds_on_vertical_lines
      ((hF n).sub (hF m)) (stripGrowth_sub (hG n) (hG m)) (ha.trans_le (huv.trans hb.le))
      hε.le (hN n m hn hm) (ha.le.trans hz) (hz'.trans hb.le)⟩
  have hCauchy (R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
      ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → ∀ z : ℂ, ‖z‖ ≤ R →
        ‖F n z - F m z‖ ≤ ε := by
    obtain ⟨A, B, hB, h⟩ := hstrips (-R) R (by linarith)
    obtain ⟨N, hN⟩ := h (ε / Real.exp (A + B * R)) (by positivity)
    refine ⟨N, fun n m hn hm z hz => ?_⟩
    obtain ⟨hl, hr⟩ := abs_le.mp ((Complex.abs_re_le_norm z).trans hz)
    refine (hN n m hn hm z hl hr).trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos _)]
    gcongr
    exact (Complex.abs_im_le_norm z).trans hz
  have hpt (z : ℂ) : CauchySeq (fun n => F n z) := by
    refine Metric.cauchySeq_iff.mpr (fun ε hε => ?_)
    obtain ⟨N, hN⟩ := hCauchy ‖z‖ (norm_nonneg z) (ε / 2) (half_pos hε)
    exact ⟨N, fun n hn m hm => (by rw [dist_eq_norm]; exact
      (hN n m hn hm z le_rfl).trans_lt (half_lt_self hε))⟩
  choose f hf using fun z => cauchySeq_tendsto_of_complete (hpt z)
  have hlim : TendstoLocallyUniformly F f atTop := by
    refine tendstoLocallyUniformly_iff_forall_isCompact.mpr fun S hS =>
      Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn continuous_id.continuousOn
    obtain ⟨N, hN⟩ := hCauchy (max R 0) (le_max_right _ _) (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with n hn z hz
    have hdist : ‖F n z - f z‖ ≤ ε / 2 := by
      apply le_of_tendsto (((tendsto_const_nhds (x := F n z)).sub (hf z)).norm)
      filter_upwards [eventually_ge_atTop N] with m hm
      exact hN n m hn hm z ((hR z hz).trans (le_max_left _ _))
    rw [dist_comm, dist_eq_norm]
    exact hdist.trans_lt (half_lt_self hε)
  refine ⟨f, hlim, differentiableOn_univ.mp
    (hlim.tendstoLocallyUniformlyOn.differentiableOn
      (.of_forall fun n => (hF n).differentiableOn) isOpen_univ), ?_⟩
  intro a b
  obtain ⟨A, B, hB, h⟩ := hstrips (min a b) b (min_le_right _ _)
  obtain ⟨N, hN⟩ := h 1 one_pos
  obtain ⟨C, K, T, hC, hK, hBound⟩ := hG N a b
  refine ⟨Real.exp A + C, max B K, T, add_nonneg (Real.exp_pos _).le hC,
    hK.trans (le_max_right _ _), ?_⟩
  intro z hz hz' hT
  have hdiff : ‖f z - F N z‖ ≤ Real.exp (A + B * |z.im|) := by
    apply le_of_tendsto (((hf z).sub tendsto_const_nhds).norm)
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa only [one_mul] using hN n N hn le_rfl z ((min_le_left a b).trans hz) hz'
  calc
    ‖f z‖ = ‖f z - F N z + F N z‖ := by rw [sub_add_cancel]
    _ ≤ ‖f z - F N z‖ + ‖F N z‖ := norm_add_le _ _
    _ ≤ Real.exp (A + B * |z.im|) + C * Real.exp (K * |z.im|) :=
      add_le_add hdiff (hBound z hz hz' hT)
    _ ≤ _ := by
      rw [Real.exp_add, add_mul]
      gcongr <;> first | exact le_max_left _ _ | exact le_max_right _ _

end Langlands.Analysis
