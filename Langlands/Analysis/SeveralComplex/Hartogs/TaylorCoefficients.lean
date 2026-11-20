import Langlands.Analysis.SeveralComplex.Hartogs.Osgood
import Langlands.Analysis.SeveralComplex.Hartogs.HartogsLemma
import Langlands.Analysis.SeveralComplex.ParametricHolomorphy
import Mathlib.Analysis.Complex.TaylorSeries

/-! # Taylor coefficients in one variable and the extension step of Hartogs' theorem

For `f : E₁ × ℂ → ℂ` we consider the Taylor coefficients of `w ↦ f (z, w)` at a point `w₁`,
written as Cauchy integrals over the circle of radius `ρ`:
`taylorCoeff f w₁ ρ k z = (2πi)⁻¹ ∮_{|w - w₁| = ρ} f (z, w) / (w - w₁) ^ (k + 1) dw`.

The main result, `differentiableOn_prod_ball_of_small`, is the extension step in the proof of
Hartogs' theorem on separately holomorphic functions: if `f` is separately holomorphic on
`B × ball w₁ R` (`B` open in a finite-dimensional space) and jointly holomorphic on the smaller
set `B × ball w₁ r`, then it is jointly holomorphic on `B × ball w₁ R`. The Taylor coefficients
are holomorphic in `z` and their growth is controlled by Hartogs' lemma
(`exists_ball_eventually_norm_le_exp`); this gives local bounds for `f`, and Osgood's lemma
(`differentiableOn_prod_of_locallyBounded`) concludes. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Metric Set Filter Real Complex Nat
open scoped Topology

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]

/-- The `k`-th Taylor coefficient at `w₁` of `w ↦ f (z, w)`, as a Cauchy integral over the
circle of radius `ρ` around `w₁`. -/
def taylorCoeff (f : E₁ × ℂ → ℂ) (w₁ : ℂ) (ρ : ℝ) (k : ℕ) (z : E₁) : ℂ :=
  (2 * π * I)⁻¹ • ∮ w in C(w₁, ρ), (1 / (w - w₁) ^ (k + 1)) • f (z, w)

omit [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] in
/-- Cauchy's integral formula for derivatives: `taylorCoeff` is the Taylor coefficient. -/
theorem taylorCoeff_eq {f : E₁ × ℂ → ℂ} {w₁ : ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) {z : E₁}
    (hz : DifferentiableOn ℂ (fun w => f (z, w)) (ball w₁ R)) (k : ℕ) :
    taylorCoeff f w₁ ρ k z = (k ! : ℂ)⁻¹ * iteratedDeriv k (fun w => f (z, w)) w₁ := by
  have h := DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul hρ k
    (hz.diffContOnCl_ball (closedBall_subset_ball hρR))
  rw [taylorCoeff, h, smul_eq_mul, smul_eq_mul]
  have h1 : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
  have h2 : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

omit [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] in
/-- The Taylor series of `w ↦ f (z, w)` at `w₁`, with the coefficients `taylorCoeff`. -/
theorem hasSum_taylorCoeff {f : E₁ × ℂ → ℂ} {w₁ : ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    {z : E₁} (hz : DifferentiableOn ℂ (fun w => f (z, w)) (ball w₁ R)) {w : ℂ}
    (hw : w ∈ ball w₁ R) :
    HasSum (fun k => taylorCoeff f w₁ ρ k z * (w - w₁) ^ k) (f (z, w)) := by
  have h := Complex.hasSum_taylorSeries_on_ball hz hw
  convert h using 1
  funext k
  rw [taylorCoeff_eq hρ hρR hz k, smul_eq_mul, smul_eq_mul]
  ring

omit [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] in
/-- **Cauchy's estimate** for `taylorCoeff`. -/
theorem norm_taylorCoeff_le {f : E₁ × ℂ → ℂ} {w₁ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {z : E₁} {M : ℝ}
    (hM : ∀ w ∈ sphere w₁ ρ, ‖f (z, w)‖ ≤ M) (k : ℕ) :
    ‖taylorCoeff f w₁ ρ k z‖ ≤ M / ρ ^ k := by
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ.le
    (C := M / ρ ^ (k + 1)) (f := fun w => (1 / (w - w₁) ^ (k + 1)) • f (z, w)) (c := w₁)
    (fun w hw => by
      have hw' := mem_sphere_iff_norm.1 hw
      rw [norm_smul, norm_div, norm_one, norm_pow, hw', one_div, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (hM w hw) (by positivity))
  calc ‖taylorCoeff f w₁ ρ k z‖ ≤ ρ * (M / ρ ^ (k + 1)) := h
    _ = M / ρ ^ k := by
      rw [pow_succ]
      field_simp

/-- The Taylor coefficients depend holomorphically on `z` where `f` is jointly continuous and
holomorphic in `z`. -/
theorem differentiableOn_taylorCoeff [FiniteDimensional ℂ E₁] {B : Set E₁} (hB : IsOpen B)
    {f : E₁ × ℂ → ℂ} {w₁ : ℂ} {ρ r R : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hρR : ρ < R)
    (hf₁ : ∀ w ∈ ball w₁ R, DifferentiableOn ℂ (fun z => f (z, w)) B)
    (hcont : ContinuousOn f (B ×ˢ ball w₁ r)) (k : ℕ) :
    DifferentiableOn ℂ (taylorCoeff f w₁ ρ k) B := by
  have hρabs : |ρ| = ρ := abs_of_pos hρ
  show DifferentiableOn ℂ
    (fun z => (2 * π * I)⁻¹ • ∮ w in C(w₁, ρ), (1 / (w - w₁) ^ (k + 1)) • f (z, w)) B
  refine DifferentiableOn.const_smul (c := (2 * π * I)⁻¹) ?_
  refine differentiableOn_circleIntegral_of_continuousOn hB
    (G := fun z w => (1 / (w - w₁) ^ (k + 1)) • f (z, w)) ?_ ?_
  · have h1 : ContinuousOn (fun p : E₁ × ℂ => 1 / (p.2 - w₁) ^ (k + 1))
        (B ×ˢ sphere w₁ |ρ|) := by
      refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
      rintro p ⟨-, hp⟩
      apply pow_ne_zero
      rw [hρabs, mem_sphere_iff_norm] at hp
      intro h
      rw [h, norm_zero] at hp
      exact hρ.ne' hp.symm
    have h2 : ContinuousOn f (B ×ˢ sphere w₁ |ρ|) := by
      rw [hρabs]
      exact hcont.mono (prod_mono subset_rfl (sphere_subset_ball hρr))
    exact h1.smul h2
  · intro t ht
    rw [hρabs] at ht
    exact (hf₁ t (sphere_subset_ball hρR ht)).const_smul (c := (1 / (t - w₁) ^ (k + 1) : ℂ))

variable [FiniteDimensional ℂ E₁]

/-- **Extension step of Hartogs' theorem.** Let `B ⊆ E₁` be open, `E₁` finite-dimensional, and
let `f : E₁ × ℂ → ℂ` be holomorphic in each variable separately on `B × ball w₁ R` and jointly
holomorphic on `B × ball w₁ r` for some `r > 0`. Then `f` is jointly holomorphic on
`B × ball w₁ R`. -/
theorem differentiableOn_prod_ball_of_small {B : Set E₁} (hB : IsOpen B) {f : E₁ × ℂ → ℂ}
    {w₁ : ℂ} {r R : ℝ} (hr : 0 < r)
    (hf₁ : ∀ w ∈ ball w₁ R, DifferentiableOn ℂ (fun z => f (z, w)) B)
    (hf₂ : ∀ z ∈ B, DifferentiableOn ℂ (fun w => f (z, w)) (ball w₁ R))
    (hsmall : DifferentiableOn ℂ f (B ×ˢ ball w₁ r)) :
    DifferentiableOn ℂ f (B ×ˢ ball w₁ R) := by
  refine differentiableOn_prod_of_locallyBounded hB isOpen_ball hf₁ hf₂ ?_
  rintro ⟨z₀, w₀⟩ ⟨hz₀, hw₀⟩
  have hR : 0 < R := pos_of_mem_ball hw₀
  -- radii: `ρ` for the Cauchy integrals, `R₂ < R₁ < R` around `w₀`
  set ρ : ℝ := min r R / 2 with hρ_def
  have hmin : 0 < min r R := lt_min hr hR
  have hρ : 0 < ρ := by positivity
  have hρr : ρ < r := by have := min_le_left r R; linarith
  have hρR : ρ < R := by have := min_le_right r R; linarith
  obtain ⟨R₂, hR₂w, hR₂R⟩ := exists_between (mem_ball.1 hw₀)
  obtain ⟨R₁, hR₂₁, hR₁R⟩ := exists_between hR₂R
  have hR₂ : 0 < R₂ := lt_of_le_of_lt dist_nonneg hR₂w
  have hR₁ : 0 < R₁ := hR₂.trans hR₂₁
  -- a closed ball around `z₀` in `B`
  obtain ⟨s, hs, hsB⟩ := Metric.isOpen_iff.1 hB z₀ hz₀
  set σ : ℝ := s / 2 with hσ_def
  have hσ : 0 < σ := by positivity
  have hcl : closedBall z₀ σ ⊆ B := (closedBall_subset_ball (by linarith)).trans hsB
  -- a uniform bound for `f` on `closedBall z₀ σ × sphere w₁ ρ`
  have hK : IsCompact (closedBall z₀ σ ×ˢ sphere w₁ ρ) :=
    (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKsub : closedBall z₀ σ ×ˢ sphere w₁ ρ ⊆ B ×ˢ ball w₁ r :=
    prod_mono hcl (sphere_subset_ball hρr)
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (hsmall.continuousOn.mono hKsub)
  have hc_bound : ∀ k, ∀ z ∈ closedBall z₀ σ, ‖taylorCoeff f w₁ ρ k z‖ ≤ M₀ / ρ ^ k :=
    fun k z hz => norm_taylorCoeff_le hρ (fun w hw => hM₀ (z, w) ⟨hz, hw⟩) k
  have hM₀0 : 0 ≤ M₀ := by
    have := hc_bound 0 z₀ (mem_closedBall_self hσ.le)
    rw [pow_zero, div_one] at this
    exact (norm_nonneg _).trans this
  -- Hartogs' lemma for `g k z = taylorCoeff f w₁ ρ k z * R₁ ^ k` on `ball z₀ σ`
  have hg_diff : ∀ k, DifferentiableOn ℂ (fun z => taylorCoeff f w₁ ρ k z * (R₁ : ℂ) ^ k)
      (ball z₀ σ) := fun k =>
    ((differentiableOn_taylorCoeff hB hρ hρr hρR hf₁ hsmall.continuousOn k).mono
      (ball_subset_closedBall.trans hcl)).mul_const _
  have hg_bound : ∀ k, ∀ z ∈ ball z₀ σ,
      ‖taylorCoeff f w₁ ρ k z * (R₁ : ℂ) ^ k‖ ≤ M₀ * (R₁ / ρ) ^ k := by
    intro k z hz
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR₁.le, div_pow]
    calc ‖taylorCoeff f w₁ ρ k z‖ * R₁ ^ k ≤ M₀ / ρ ^ k * R₁ ^ k :=
          mul_le_mul_of_nonneg_right (hc_bound k z (ball_subset_closedBall hz)) (by positivity)
      _ = M₀ * (R₁ ^ k / ρ ^ k) := by ring
  have hg_lim : ∀ z ∈ ball z₀ σ, ∀ᶠ k in atTop, ‖taylorCoeff f w₁ ρ k z * (R₁ : ℂ) ^ k‖ ≤ 1 := by
    intro z hz
    have hzB : z ∈ B := hcl (ball_subset_closedBall hz)
    have hw : w₁ + (R₁ : ℂ) ∈ ball w₁ R := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg hR₁.le]
      exact hR₁R
    have ht := (hasSum_taylorCoeff hρ hρR (hf₂ z hzB) hw).summable.tendsto_atTop_zero
    simp only [add_sub_cancel_left] at ht
    have htn := ht.norm
    rw [norm_zero] at htn
    filter_upwards [(tendsto_order.1 htn).2 1 one_pos] with k hk
    exact hk.le
  set ε : ℝ := Real.log (R₁ / R₂) / 2 with hε_def
  have hlogpos : 0 < Real.log (R₁ / R₂) := Real.log_pos ((one_lt_div hR₂).2 hR₂₁)
  have hε : 0 < ε := by positivity
  obtain ⟨δ, hδ, hev⟩ := exists_ball_eventually_norm_le_exp isOpen_ball hg_diff hg_bound hg_lim
    (mem_ball_self hσ) hε
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  -- the geometric ratio `q < 1`
  set q : ℝ := Real.exp ε * (R₂ / R₁) with hq_def
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    have h1 : Real.exp ε < R₁ / R₂ := by
      rw [← Real.exp_log (div_pos hR₁ hR₂)]
      exact Real.exp_lt_exp.2 (by linarith)
    calc q < R₁ / R₂ * (R₂ / R₁) := mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 1 := by field_simp
  -- the summable majorant
  set b : ℕ → ℝ := fun k => (if k < K then M₀ / ρ ^ k * R₂ ^ k else 0) + Real.exp ε * q ^ k
    with hb_def
  have hb_sum : Summable b := by
    refine Summable.add ?_ ((summable_geometric_of_lt_one hq0 hq1).mul_left _)
    refine summable_of_ne_finset_zero (s := Finset.range K) fun k hk => ?_
    simp only [Finset.mem_range] at hk
    simp [hk]
  refine ⟨∑' k, b k, ?_⟩
  have hnhds : ball z₀ (min δ σ) ×ˢ ball w₁ R₂ ∈ 𝓝 (z₀, w₀) :=
    prod_mem_nhds (ball_mem_nhds _ (lt_min hδ hσ)) (isOpen_ball.mem_nhds (mem_ball.2 hR₂w))
  filter_upwards [hnhds] with ⟨y, w⟩ ⟨hy, hw⟩
  have hyσ : y ∈ ball z₀ σ := ball_subset_ball (min_le_right _ _) hy
  have hyδ : y ∈ ball z₀ δ := ball_subset_ball (min_le_left _ _) hy
  have hyB : y ∈ B := hcl (ball_subset_closedBall hyσ)
  have hwR : w ∈ ball w₁ R := ball_subset_ball hR₂R.le hw
  have hsum := hasSum_taylorCoeff hρ hρR (hf₂ y hyB) hwR
  rw [← hsum.tsum_eq]
  refine tsum_of_norm_bounded hb_sum.hasSum fun k => ?_
  have hwn : ‖w - w₁‖ ≤ R₂ := by
    rw [mem_ball, dist_eq_norm] at hw
    exact hw.le
  have hpow : ‖w - w₁‖ ^ k ≤ R₂ ^ k := pow_le_pow_left₀ (norm_nonneg _) hwn k
  rw [norm_mul, norm_pow]
  have hgeom : 0 ≤ Real.exp ε * q ^ k := by positivity
  by_cases hk : k < K
  · -- Cauchy's estimate for the first `K` coefficients
    have h1 : ‖taylorCoeff f w₁ ρ k y‖ * ‖w - w₁‖ ^ k ≤ M₀ / ρ ^ k * R₂ ^ k :=
      mul_le_mul (hc_bound k y (ball_subset_closedBall hyσ)) hpow (by positivity)
        (by positivity)
    simp only [hb_def, hk, ite_true]
    linarith
  · -- Hartogs' lemma for the others
    have hgk : ‖taylorCoeff f w₁ ρ k y * (R₁ : ℂ) ^ k‖ ≤ Real.exp ((k + 1) * ε) :=
      hK k (not_lt.1 hk) y hyδ
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR₁.le] at hgk
    have hcy : ‖taylorCoeff f w₁ ρ k y‖ ≤ Real.exp ((k + 1) * ε) / R₁ ^ k := by
      rw [le_div_iff₀ (by positivity)]
      exact hgk
    have h1 : ‖taylorCoeff f w₁ ρ k y‖ * ‖w - w₁‖ ^ k ≤
        Real.exp ((k + 1) * ε) / R₁ ^ k * R₂ ^ k :=
      mul_le_mul hcy hpow (by positivity) (by positivity)
    have h2 : Real.exp ((k + 1) * ε) / R₁ ^ k * R₂ ^ k = Real.exp ε * q ^ k := by
      rw [hq_def, mul_pow, div_pow, show ((k : ℝ) + 1) * ε = ε + k * ε by ring, Real.exp_add,
        Real.exp_nat_mul]
      field_simp
    simp only [hb_def, hk, ite_false, zero_add]
    linarith

end Langlands.Analysis.SeveralComplex
