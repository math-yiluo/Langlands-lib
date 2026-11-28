import Langlands.Global.RankinSelberg.ArchimedeanMellinPair
import Langlands.Global.RankinSelberg.OrdinarySemilocalNormalization
import Langlands.LocalFactor.Archimedean.GammaStripGrowth
import Mathlib.Analysis.Complex.PhragmenLindelof

/-! # Strip growth of normalizations from a Mellin pair -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Asymptotics Filter MeasureTheory Set

universe u v

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinPair

open LocalFactor LocalFactor.Archimedean

private theorem norm_mul_exp_sq_div (f : ℂ → ℂ) (m : ℝ) (s : ℂ) :
    ‖f s * Complex.exp (s ^ 2 / (m : ℂ))‖ =
      ‖f s‖ * Real.exp ((s.re ^ 2 - s.im ^ 2) / m) := by
  simp only [norm_mul, Complex.norm_exp, Complex.div_ofReal_re, pow_two, Complex.mul_re]

private theorem re_sq_le_strip {a b : ℝ} {s : ℂ} (hsa : a ≤ s.re) (hsb : s.re ≤ b) :
    s.re ^ 2 ≤ (|a| + |b|) ^ 2 := by
  have h : |s.re| ≤ |a| + |b| := abs_le.mpr
    ⟨by linarith [neg_abs_le a, abs_nonneg b], by linarith [le_abs_self b, abs_nonneg a]⟩
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg s.re) h 2

/-- A Gaussian bound on a vertical strip propagates exponential edge bounds to its interior.
The Gaussian multiplier has parameter `1 / |z.im|` at the point of evaluation. -/
theorem norm_le_exp_of_gaussian_on_strip {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a b C A K : ℝ} (hab : a < b) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hg : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ C * Real.exp (A * s.im ^ 2))
    (he : ∀ s : ℂ, (s.re = a ∨ s.re = b) → ‖f s‖ ≤ C * Real.exp (K * |s.im|))
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) (hz : 1 ≤ |z.im|) :
    ‖f z‖ ≤ (C * Real.exp ((|a| + |b|) ^ 2)) * Real.exp ((K ^ 2 + 1) * |z.im|) := by
  let m := |z.im|
  let B := (|a| + |b|) ^ 2
  let g (s : ℂ) := f s * Complex.exp (s ^ 2 / (m : ℂ))
  have hm : 0 < m := zero_lt_one.trans_le hz
  have hB : 0 ≤ B := sq_nonneg _
  have hgDiff : Differentiable ℂ g :=
    hf.mul (Complex.differentiable_exp.comp ((differentiable_id.pow 2).div_const _))
  have hre (s : ℂ) (ha : a ≤ s.re) (hb : s.re ≤ b) : s.re ^ 2 / m ≤ B :=
    (div_le_iff₀ hm).mpr ((re_sq_le_strip ha hb).trans (le_mul_of_one_le_right hB hz))
  have hquad (y : ℝ) : K * |y| - y ^ 2 / m ≤ K ^ 2 * m := by
    calc
      _ = ((K * m) * |y| - y ^ 2) / m := by field_simp
      _ ≤ (K * m) ^ 2 / m := by
        apply div_le_div_of_nonneg_right _ hm.le
        nlinarith [sq_nonneg (K * m / 2 - |y|), sq_nonneg (K * m), sq_abs y]
      _ = _ := by field_simp
  have hgEdge (s : ℂ) (hs : s.re = a ∨ s.re = b) : ‖g s‖ ≤ C * Real.exp (B + K ^ 2 * m) := by
    have hsr : a ≤ s.re ∧ s.re ≤ b := hs.elim (fun h => ⟨h.ge, h.le.trans hab.le⟩)
      (fun h => ⟨hab.le.trans h.ge, h.le⟩)
    change ‖f s * Complex.exp (s ^ 2 / (m : ℂ))‖ ≤ _
    rw [norm_mul_exp_sq_div]
    calc
      _ ≤ (C * Real.exp (K * |s.im|)) * Real.exp ((s.re ^ 2 - s.im ^ 2) / m) :=
        mul_le_mul_of_nonneg_right (he s hs) (Real.exp_pos _).le
      _ = C * Real.exp (K * |s.im| + (s.re ^ 2 - s.im ^ 2) / m) := by
        rw [Real.exp_add, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        rw [sub_div]
        linarith [hre s hsr.1 hsr.2, hquad s.im])) hC
  let η := (Real.pi / (b - a)) / 2
  have hη : 0 < η := half_pos (div_pos Real.pi_pos (sub_pos.mpr hab))
  have hη' : η < Real.pi / (b - a) :=
    half_lt_self (div_pos Real.pi_pos (sub_pos.mpr hab))
  have hG : ∃ c < Real.pi / (b - a), ∃ D,
      g =O[comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b)]
        fun s => Real.exp (D * Real.exp (c * |s.im|)) := by
    refine ⟨η, hη', 2 * A / η ^ 2, IsBigO.of_bound (C * Real.exp B) ?_⟩
    filter_upwards [show ∀ᶠ s : ℂ in comap (abs ∘ Complex.im) atTop ⊓
        𝓟 (Complex.re ⁻¹' Ioo a b), s ∈ Complex.re ⁻¹' Ioo a b from
      mem_inf_of_right (mem_principal_self _)] with s hs
    have hEstimate : A * s.im ^ 2 ≤ (2 * A / η ^ 2) * Real.exp (η * |s.im|) := by
      have hn := mul_nonneg hη.le (abs_nonneg s.im)
      have hexp : (η * |s.im|) ^ 2 / 2 ≤ Real.exp (η * |s.im|) :=
        (le_add_of_nonneg_left (add_nonneg zero_le_one hn)).trans (Real.quadratic_le_exp_of_nonneg hn)
      calc
        _ = (2 * A / η ^ 2) * ((η * |s.im|) ^ 2 / 2) := by
          rw [mul_pow, sq_abs]
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
    change ‖f s * Complex.exp (s ^ 2 / (m : ℂ))‖ ≤ _
    rw [norm_mul_exp_sq_div, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (C * Real.exp (A * s.im ^ 2)) * Real.exp B :=
        mul_le_mul (hg s hs.1.le hs.2.le)
          (Real.exp_le_exp.mpr (by
            rw [sub_div]
            exact (sub_le_self _ (div_nonneg (sq_nonneg _) hm.le)).trans (hre s hs.1.le hs.2.le)))
          (Real.exp_pos _).le (mul_nonneg hC (Real.exp_pos _).le)
      _ ≤ _ := by
        rw [mul_right_comm C]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hEstimate) (by positivity)
  have hPL : ‖g z‖ ≤ C * Real.exp (B + K ^ 2 * m) :=
    PhragmenLindelof.vertical_strip hgDiff.diffContOnCl hG
      (fun s hs => hgEdge s (Or.inl hs)) (fun s hs => hgEdge s (Or.inr hs)) hza hzb
  have hUndo : (z.im ^ 2 - z.re ^ 2) / m ≤ m := by
    apply (div_le_iff₀ hm).mpr
    simpa only [← pow_two m, m, sq_abs] using sub_le_self (z.im ^ 2) (sq_nonneg z.re)
  calc
    ‖f z‖ = ‖g z‖ * Real.exp ((z.im ^ 2 - z.re ^ 2) / m) := by
      dsimp only [g]
      rw [norm_mul_exp_sq_div, mul_assoc, ← Real.exp_add]
      rw [show (z.re ^ 2 - z.im ^ 2) / m + (z.im ^ 2 - z.re ^ 2) / m = 0 by ring,
        Real.exp_zero, mul_one]
    _ ≤ (C * Real.exp (B + K ^ 2 * m)) * Real.exp m :=
      mul_le_mul hPL (Real.exp_le_exp.mpr hUndo) (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [Real.exp_add B, mul_assoc C, mul_assoc (Real.exp B), ← Real.exp_add,
        show K ^ 2 * m + m = (K ^ 2 + 1) * m by ring, ← mul_assoc]

private theorem vertical_line_bound {f : ℂ → ℂ} (hf : Continuous f) (a : ℝ)
    {C K T : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (h : ∀ s : ℂ, s.re = a → T ≤ |s.im| → ‖f s‖ ≤ C * Real.exp (K * |s.im|)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ, s.re = a → ‖f s‖ ≤ D * Real.exp (K * |s.im|) := by
  let B := max T 0
  let g (y : ℝ) := ‖f (⟨a, y⟩ : ℂ)‖
  have hg : Continuous g := by
    have hc : Continuous (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I) := by fun_prop
    have he (y : ℝ) : (⟨a, y⟩ : ℂ) = (a : ℂ) + (y : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    simpa only [g, he, Function.comp_apply] using (hf.comp hc).norm
  obtain ⟨M, hM⟩ := (isCompact_Icc.image (f := g) hg (s := Icc (-B) B)).bddAbove
  refine ⟨max C M, hC.trans (le_max_left _ _), fun s hs => ?_⟩
  by_cases hT : T ≤ |s.im|
  · exact (h s hs hT).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have hsmall : s.im ∈ Icc (-B) B :=
      abs_le.mp ((lt_of_not_ge hT).le.trans (le_max_left _ _))
    have heq : (⟨a, s.im⟩ : ℂ) = s := Complex.ext hs.symm rfl
    have hnorm : ‖f s‖ ≤ M := by simpa only [g, heq] using hM (mem_image_of_mem g hsmall)
    exact (hnorm.trans (le_max_right _ _)).trans
      (le_mul_of_one_le_right (hC.trans (le_max_left _ _))
        (Real.one_le_exp (mul_nonneg hK (abs_nonneg s.im))))

private theorem norm_mellin_neg_le_on_strip {φ : ℝ → ℂ} (hφ : RapidDecay φ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖mellin φ (-s)‖ ≤ C := by
  obtain ⟨C₀, h₀⟩ := hφ (b + 1)
  obtain ⟨C₁, h₁⟩ := hφ (a - 1)
  have hC₀ := RapidDecay.nonneg_const h₀
  have hC₁ := RapidDecay.nonneg_const h₁
  let w (t : ℝ) := if t ≤ 1 then C₀ else C₁ * t ^ (-2 : ℝ)
  have hw : IntegrableOn w (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    apply IntegrableOn.union
    · refine (integrableOn_const (C := C₀) (by simp : volume (Ioc (0 : ℝ) 1) ≠ ⊤)).congr_fun
        (fun t ht => ?_) measurableSet_Ioc
      simp [w, ht.2]
    · have hi : IntegrableOn (fun t : ℝ => C₁ * t ^ (-2 : ℝ)) (Ioi 1) :=
        ((integrableOn_Ioi_rpow_iff (s := -2) one_pos).2 (by norm_num)).const_mul C₁
      exact hi.congr_fun (fun t (ht : 1 < t) => by simp [w, not_le.mpr ht]) measurableSet_Ioi
  have hnonneg (t : ℝ) : 0 ≤ w t := by
    dsimp only [w]
    split_ifs with ht
    · exact hC₀
    · exact mul_nonneg hC₁ (Real.rpow_nonneg ((zero_lt_one.trans (lt_of_not_ge ht)).le) _)
  refine ⟨∫ t in Ioi (0 : ℝ), w t, integral_nonneg hnonneg, fun s ha hb => ?_⟩
  refine norm_integral_le_of_norm_le hw ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => ?_))
  change ‖(t : ℂ) ^ (-s - 1) • φ t‖ ≤ w t
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.neg_re, Complex.one_re]
  by_cases h : t ≤ 1
  · simp only [w, ite_eq_left h]
    calc
      _ ≤ t ^ (-b - 1) * (C₀ * t ^ (b + 1)) := mul_le_mul
        (Real.rpow_le_rpow_of_exponent_ge ht h (by linarith)) (h₀ t ht)
        (norm_nonneg _) (Real.rpow_nonneg ht.le _)
      _ = C₀ := by
        rw [mul_left_comm, ← Real.rpow_add ht, show -b - 1 + (b + 1) = 0 by ring,
          Real.rpow_zero, mul_one]
  · simp only [w, ite_eq_right h]
    calc
      _ ≤ t ^ (-a - 1) * (C₁ * t ^ (a - 1)) := mul_le_mul
        (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) (by linarith)) (h₁ t ht)
        (norm_nonneg _) (Real.rpow_nonneg ht.le _)
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add ht, show -a - 1 + (a - 1) = -2 by ring]

private theorem norm_determinant_mellin_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (F : X → ℂ) (δ : X → ℝ) (hδ : ∀ x, 0 < δ x) {s : ℂ}
    (h : Integrable (fun x => ‖F x‖ * δ x ^ s.re) μ) :
    ‖∫ x, F x * (δ x : ℂ) ^ s ∂μ‖ ≤ ∫ x, ‖F x‖ * δ x ^ s.re ∂μ := by
  refine norm_integral_le_of_norm_le h (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ x)]

private theorem norm_le_on_strip_of_norm_re {E : ℂ → ℂ} (hE : Continuous E)
    (hEn : ∀ s : ℂ, ‖E s‖ = ‖E (s.re : ℂ)‖) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖E s‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image (hE.comp Complex.continuous_ofReal).norm
    (s := Icc a b)).bddAbove
  refine ⟨max C 0, le_max_right _ _, fun s ha hb => ?_⟩
  rw [hEn s]
  exact (hC (mem_image_of_mem (fun x : ℝ => ‖E (x : ℂ)‖) ⟨ha, hb⟩)).trans (le_max_left _ _)

/-- A Gaussian Mellin pair produces an entire value of exponential strip growth with the
specified ordinary and reflected values in their half-planes. Here `E` is the inverse of
the signed reflection factor. -/
def MellinPairEntireValueStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (F : X → ℂ) (δ : X → ℝ) (G : Y → ℂ) (δd : Y → ℝ)
    (h k : ℝ → ℂ) (N : ℝ) (L Ld : ReciprocalEntire) (E : ℂ → ℂ),
    AEStronglyMeasurable F μ → AEStronglyMeasurable G ν →
    Measurable δ → Measurable δd → (∀ x, 0 < δ x) → (∀ y, 0 < δd y) →
    Measurable h → Measurable k → RapidDecay h → RapidDecay k →
    (∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖F x‖ * δ x ^ σ) μ) →
    (∀ σ : ℝ, N ≤ σ → Integrable (fun y => ‖G y‖ * δd y ^ σ) ν) →
    (∀ a : ℝ, 0 < a → theta μ F δ h a = (a : ℂ) * theta ν G δd k a⁻¹) →
    (∀ s : ℂ, E s * mellin h (-s) = Complex.exp (s ^ 2) * L.denominator s) →
    (∀ s : ℂ, mellin k (s - 1) = Complex.exp (s ^ 2) * Ld.denominator (1 - s)) →
    Differentiable ℂ E → (∀ s : ℂ, ‖E s‖ = ‖E (s.re : ℂ)‖) →
    HasStripExponentialGrowth L.denominator → HasStripExponentialGrowth Ld.denominator →
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ HasStripExponentialGrowth R ∧
      (∀ s : ℂ, N ≤ s.re → R s = (∫ x, F x * (δ x : ℂ) ^ s ∂μ) * L.denominator s) ∧
      (∀ s : ℂ, s.re ≤ 1 - N →
        R s = E s * ((∫ y, G y * (δd y : ℂ) ^ (1 - s) ∂ν) * Ld.denominator (1 - s)))

theorem mellinPairEntireValue : MellinPairEntireValueStatement.{u, v} := by
  intro X Y _ _ μ ν _ _ F δ G δd h k N L Ld E hF hG hδm hδdm hδ hδd hh hk hhdec hkdec
    hFN hGN hpair hMh hMk hEa hEn hL hLd
  obtain ⟨hΘ, hΘr, hΘl⟩ := mellin_theta_entire μ ν F δ G δd hF hG hδm hδdm hδ hδd h k
    hh hk hhdec hkdec N hFN hGN hpair
  let R (s : ℂ) := E s * Complex.exp (-(s ^ 2)) * mellin (theta μ F δ h) (-s)
  have hRa : Differentiable ℂ R := (hEa.mul (Complex.differentiable_exp.comp
    (differentiable_id.pow 2).neg)).mul hΘ
  have hRight (s : ℂ) (hs : N ≤ s.re) :
      R s = (∫ x, F x * (δ x : ℂ) ^ s ∂μ) * L.denominator s := by
    dsimp only [R]
    rw [hΘr s hs]
    calc
      _ = (∫ x, F x * (δ x : ℂ) ^ s ∂μ) * (Complex.exp (-(s ^ 2)) * (E s * mellin h (-s))) := by ring
      _ = _ := by rw [hMh s, ← mul_assoc (Complex.exp (-(s ^ 2))), ← Complex.exp_add,
        neg_add_cancel, Complex.exp_zero, one_mul]
  have hLeft (s : ℂ) (hs : s.re ≤ 1 - N) :
      R s = E s * ((∫ y, G y * (δd y : ℂ) ^ (1 - s) ∂ν) * Ld.denominator (1 - s)) := by
    dsimp only [R]
    rw [hΘl s hs, hMk s]
    calc
      _ = E s * ((∫ y, G y * (δd y : ℂ) ^ (1 - s) ∂ν) *
        ((Complex.exp (-(s ^ 2)) * Complex.exp (s ^ 2)) * Ld.denominator (1 - s))) := by ring
      _ = _ := by rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  have hGauss (a b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖R s‖ ≤ C * Real.exp (s.im ^ 2) := by
    obtain ⟨C, hC, hB⟩ := norm_mellin_neg_le_on_strip
      (theta_rapidDecay μ ν F δ G δd hδ hδd hhdec hkdec hFN hGN hpair) a b
    obtain ⟨M, hM, hME⟩ := norm_le_on_strip_of_norm_re hEa.continuous hEn a b
    refine ⟨M * C, mul_nonneg hM hC, fun s ha hb => ?_⟩
    have hExp : ‖Complex.exp (-(s ^ 2))‖ ≤ Real.exp (s.im ^ 2) := by
      rw [Complex.norm_exp, Complex.neg_re, pow_two, Complex.mul_re]
      exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg s.re])
    simp only [R, norm_mul]
    calc
      _ ≤ (M * Real.exp (s.im ^ 2)) * C :=
        mul_le_mul (mul_le_mul (hME s ha hb) hExp (norm_nonneg _) hM)
          (hB s ha hb) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hRline (b : ℝ) (hb : N ≤ b) : ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ s : ℂ, s.re = b → ‖R s‖ ≤ C * Real.exp (K * |s.im|) := by
    obtain ⟨C, K, T, hC, hK, hB⟩ := hL b b
    let D := ∫ x, ‖F x‖ * δ x ^ b ∂μ
    have hD : 0 ≤ D := integral_nonneg fun x => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hδ x).le _)
    have htail (s : ℂ) (hs : s.re = b) (ht : T ≤ |s.im|) :
        ‖R s‖ ≤ (D * C) * Real.exp (K * |s.im|) := by
      have hsN : N ≤ s.re := hs.symm ▸ hb
      have hI := norm_determinant_mellin_le F δ hδ (hFN s.re hsN)
      rw [hs] at hI
      rw [hRight s hsN, norm_mul, mul_assoc]
      exact mul_le_mul hI (hB s hs.ge hs.le ht) (norm_nonneg _) hD
    obtain ⟨M, hM, hMR⟩ := vertical_line_bound hRa.continuous b (mul_nonneg hD hC) hK htail
    exact ⟨M, K, hM, hK, hMR⟩
  have hLline (a : ℝ) (ha : a ≤ 1 - N) : ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ s : ℂ, s.re = a → ‖R s‖ ≤ C * Real.exp (K * |s.im|) := by
    obtain ⟨C, K, T, hC, hK, hB⟩ := hLd (1 - a) (1 - a)
    let D := ∫ y, ‖G y‖ * δd y ^ (1 - a) ∂ν
    have hD : 0 ≤ D := integral_nonneg fun x => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hδd x).le _)
    let M := ‖E (a : ℂ)‖
    have hM : 0 ≤ M := norm_nonneg _
    have htail (s : ℂ) (hs : s.re = a) (ht : T ≤ |s.im|) :
        ‖R s‖ ≤ (M * (D * C)) * Real.exp (K * |s.im|) := by
      have hre : (1 - s).re = 1 - a := by simp only [Complex.sub_re, Complex.one_re, hs]
      have him : |(1 - s).im| = |s.im| := by simp
      have hsN : N ≤ (1 - s).re := by rw [hre]; linarith
      have hI := norm_determinant_mellin_le G δd hδd (hGN (1 - s).re hsN)
      rw [hre] at hI
      have hB' := hB (1 - s) hre.ge hre.le (him.symm ▸ ht)
      rw [him] at hB'
      rw [hLeft s (hs.symm ▸ ha), norm_mul, norm_mul, hEn, hs, mul_assoc M, mul_assoc D]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hI hB' (norm_nonneg _) hD) hM
    obtain ⟨U, hU, hUR⟩ := vertical_line_bound hRa.continuous a
      (mul_nonneg hM (mul_nonneg hD hC)) hK htail
    exact ⟨U, K, hU, hK, hUR⟩
  refine ⟨R, hRa, ?_, hRight, hLeft⟩
  intro a b
  let l := min a (1 - N) - 1
  let r := max (max a b) N + 1
  have hl : l < min a (1 - N) := sub_lt_self _ zero_lt_one
  have hr : max (max a b) N < r := lt_add_one _
  have hla : l < a := hl.trans_le (min_le_left _ _)
  have har : a < r := ((le_max_left a b).trans (le_max_left _ _)).trans_lt hr
  have hbr : b < r := ((le_max_right a b).trans (le_max_left _ _)).trans_lt hr
  obtain ⟨Cl, Kl, _, _, hEl⟩ := hLline l (hl.le.trans (min_le_right _ _))
  obtain ⟨Cr, Kr, _, _, hEr⟩ := hRline r ((le_max_right _ _).trans hr.le)
  obtain ⟨Cq, hCq, hQ⟩ := hGauss l r
  let C := max Cq (max Cl Cr)
  let K := max Kl Kr
  have hC : 0 ≤ C := hCq.trans (le_max_left _ _)
  refine ⟨C * Real.exp ((|l| + |r|) ^ 2), K ^ 2 + 1, 1, by positivity, by positivity,
    fun s ha hb ht => ?_⟩
  apply norm_le_exp_of_gaussian_on_strip hRa (hla.trans har) hC zero_le_one
    (fun w hw hw' => ?_) (fun w hw => ?_) (hla.le.trans ha) (hb.trans hbr.le) ht
  · simpa only [one_mul] using (hQ w hw hw').trans
      (mul_le_mul_of_nonneg_right (le_max_left Cq (max Cl Cr)) (Real.exp_pos _).le)
  · rcases hw with hw | hw
    · exact (hEl w hw).trans (mul_le_mul ((le_max_left Cl Cr).trans (le_max_right _ _))
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
        (Real.exp_pos _).le hC)
    · exact (hEr w hw).trans (mul_le_mul ((le_max_right Cl Cr).trans (le_max_right _ _))
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)))
        (Real.exp_pos _).le hC)

/-- A Gaussian Mellin pair and exponential bounds for the two reciprocal L-denominators
give an entire normalization of exponential strip growth. Here `E` is the inverse of
the signed epsilon factor. -/
def MellinPairNormalizedStripGrowthStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (F : X → ℂ) (δ : X → ℝ) (G : Y → ℂ) (δd : Y → ℝ)
    (h k : ℝ → ℂ) (N : ℝ) (L Ld : ReciprocalEntire) (E : ℂ → ℂ),
    AEStronglyMeasurable F μ → AEStronglyMeasurable G ν →
    Measurable δ → Measurable δd → (∀ x, 0 < δ x) → (∀ y, 0 < δd y) →
    Measurable h → Measurable k → RapidDecay h → RapidDecay k →
    (∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖F x‖ * δ x ^ σ) μ) →
    (∀ σ : ℝ, N ≤ σ → Integrable (fun y => ‖G y‖ * δd y ^ σ) ν) →
    (∀ a : ℝ, 0 < a → theta μ F δ h a = (a : ℂ) * theta ν G δd k a⁻¹) →
    (∀ s : ℂ, E s * mellin h (-s) = Complex.exp (s ^ 2) * L.denominator s) →
    (∀ s : ℂ, mellin k (s - 1) = Complex.exp (s ^ 2) * Ld.denominator (1 - s)) →
    Differentiable ℂ E → (∀ s : ℂ, ‖E s‖ = ‖E (s.re : ℂ)‖) →
    HasStripExponentialGrowth L.denominator → HasStripExponentialGrowth Ld.denominator →
    (∃ τ : ℝ, ∀ s : ℂ, τ < s.re → L.denominator s ≠ 0) →
    ∃ R : OrdinaryIntegralNormalization (fun s => ∫ x, F x * (δ x : ℂ) ^ s ∂μ)
      (fun s => (L.denominator s)⁻¹), HasStripExponentialGrowth R.value

theorem mellinPairNormalizedStripGrowth : MellinPairNormalizedStripGrowthStatement.{u, v} := by
  intro X Y _ _ μ ν _ _ F δ G δd h k N L Ld E hF hG hδm hδdm hδ hδd hh hk hhdec hkdec
    hFN hGN hpair hMh hMk hEa hEn hL hLd hLne
  obtain ⟨R, hR, hGrowth, hRight, _⟩ := mellinPairEntireValue μ ν F δ G δd h k N L Ld E
    hF hG hδm hδdm hδ hδd hh hk hhdec hkdec hFN hGN hpair hMh hMk hEa hEn hL hLd
  obtain ⟨τ, hτ⟩ := hLne
  refine ⟨⟨R, fun s _ => hR.analyticAt s, ⟨max N τ, fun s hs => ?_⟩⟩, hGrowth⟩
  rw [hRight s ((le_max_left _ _).trans hs.le), mul_assoc,
    mul_inv_cancel₀ (hτ s ((le_max_right _ _).trans_lt hs)), mul_one]

end Langlands.Global.RankinSelbergGlobal.ArchimedeanMellinPair
