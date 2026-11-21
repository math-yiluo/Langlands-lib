import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Holomorphic functions of several complex variables are smooth

A function `f : E → F` on a finite-dimensional complex normed space that is complex
differentiable on an open set `U` is infinitely complex differentiable on `U`
(`contDiffOn_of_differentiableOn`). Mathlib proves this for functions of one complex variable
(`DifferentiableOn.contDiffOn`).

The proof restricts `f` to complex lines. For `z ∈ U` and a direction `v`, the one-variable
Cauchy formula for the first derivative of `t ↦ f (z + t v)` gives
`f'(z) v = (2πi)⁻¹ ∮_{|t| = R} t⁻² f (z + t v) dt`
(`fderiv_apply_eq_integral`), with one radius `R` for all `z` near a given point. This integral
depends continuously on `z`, so `f'` is continuous on `U`; differentiating under the integral
sign then shows that `z ↦ f'(z) v` is complex differentiable, so `f'` is complex
differentiable on `U` (`differentiableOn_fderiv`). Induction on the order gives smoothness. -/

noncomputable section
set_option autoImplicit false

open Complex Metric Set Filter Topology MeasureTheory
open scoped Real ContDiff

namespace Langlands.Analysis.HolomorphicContDiff

universe u

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The kernel `(d/dθ) circleMap 0 R θ / (circleMap 0 R θ)²` of the Cauchy formula for the first
derivative, written as an integral over `θ ∈ [0, 2π]`. -/
def kernel (R θ : ℝ) : ℂ := deriv (circleMap 0 R) θ * (1 / (circleMap 0 R θ - 0) ^ 2)

theorem continuous_kernel {R : ℝ} (hR : R ≠ 0) : Continuous (kernel R) := by
  unfold kernel
  simp only [deriv_circleMap]
  refine ((continuous_circleMap 0 R).mul continuous_const).mul
    (continuous_const.div (((continuous_circleMap 0 R).sub continuous_const).pow 2) ?_)
  intro θ
  exact pow_ne_zero 2 (by simpa using circleMap_ne_center (c := 0) (θ := θ) hR)

theorem norm_kernel {R : ℝ} (hR : 0 < R) (θ : ℝ) : ‖kernel R θ‖ = R⁻¹ := by
  simp only [kernel, deriv_circleMap, sub_zero, norm_mul, norm_div, norm_pow, norm_one,
    norm_circleMap_zero, norm_I, abs_of_pos hR]
  field_simp

theorem circleIntegral_eq (f : ℂ → F) (R : ℝ) :
    (∮ t in C(0, R), (1 / (t - 0) ^ 2) • f t) =
      ∫ θ in (0 : ℝ)..2 * π, kernel R θ • f (circleMap 0 R θ) := by
  simp only [circleIntegral, kernel, mul_smul]

variable [CompleteSpace F]

/-- The Cauchy formula for the derivative along a complex line: if `f` is complex differentiable
on the open set `U` and `z + t v ∈ U` for `‖t‖ ≤ R`, then
`f'(z) v = (2πi)⁻¹ ∫_0^{2π} kernel R θ • f (z + circleMap 0 R θ • v) dθ`. -/
theorem fderiv_apply_eq_integral {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z v : E} {R : ℝ} (hR : 0 < R)
    (hzU : ∀ t : ℂ, ‖t‖ ≤ R → z + t • v ∈ U) :
    fderiv ℂ f z v =
      (2 * π * I)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, kernel R θ • f (z + circleMap 0 R θ • v) := by
  set g : ℂ → F := fun t => f (z + t • v) with hg
  have hgd : ∀ t : ℂ, ‖t‖ ≤ R → HasDerivAt g (fderiv ℂ f (z + t • v) v) t := by
    intro t ht
    have hfd : HasFDerivAt f (fderiv ℂ f (z + t • v)) (z + t • v) :=
      (hf.differentiableAt (hU.mem_nhds (hzU t ht))).hasFDerivAt
    have hl : HasDerivAt (fun t : ℂ => z + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add z
    exact hfd.comp_hasDerivAt t hl
  have hdiff : DifferentiableOn ℂ g (closedBall 0 R) := fun t ht =>
    (hgd t (by simpa using ht)).differentiableAt.differentiableWithinAt
  have h := hdiff.deriv_eq_smul_circleIntegral hR
  rw [(hgd 0 (by simp [hR.le])).deriv, zero_smul, add_zero] at h
  have h' : (∫ θ in (0 : ℝ)..2 * π, kernel R θ • f (z + circleMap 0 R θ • v)) =
      (2 * π * I) • fderiv ℂ f z v := by
    rw [← h, circleIntegral_eq]
  rw [h', smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]

/-- Around a point `z₀` of an open set `U` and for a direction `v` there are `R, ε > 0` with
`closedBall z₀ (2ε) ⊆ U` and `z + t v ∈ closedBall z₀ (2ε)` for `z ∈ ball z₀ ε`, `‖t‖ ≤ R`. -/
theorem exists_radius {U : Set E} (hU : IsOpen U) {z₀ : E} (hz₀ : z₀ ∈ U) (v : E) :
    ∃ R > 0, ∃ ε > 0, closedBall z₀ (2 * ε) ⊆ U ∧
      ∀ z ∈ ball z₀ ε, ∀ t : ℂ, ‖t‖ ≤ R → z + t • v ∈ closedBall z₀ (2 * ε) := by
  obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hε : 0 < ε' / 4 := by positivity
  refine ⟨ε' / 4 / (‖v‖ + 1), by positivity, ε' / 4, hε,
    (closedBall_subset_ball (by linarith)).trans hball, ?_⟩
  intro z hz t ht
  rw [mem_closedBall, dist_eq_norm]
  rw [mem_ball, dist_eq_norm] at hz
  have hv : ‖t‖ * ‖v‖ ≤ ε' / 4 := by
    calc ‖t‖ * ‖v‖ ≤ ε' / 4 / (‖v‖ + 1) * (‖v‖ + 1) :=
          mul_le_mul ht (by linarith) (norm_nonneg _) (by positivity)
      _ = ε' / 4 := div_mul_cancel₀ _ (by positivity)
  calc ‖z + t • v - z₀‖ = ‖(z - z₀) + t • v‖ := by congr 1; abel
    _ ≤ ‖z - z₀‖ + ‖t • v‖ := norm_add_le _ _
    _ ≤ ε' / 4 + ε' / 4 := by rw [norm_smul]; linarith
    _ = 2 * (ε' / 4) := by ring

theorem norm_circleMap_le {R : ℝ} (hR : 0 < R) (θ : ℝ) : ‖circleMap 0 R θ‖ ≤ R := by
  rw [norm_circleMap_zero, abs_of_pos hR]

variable [FiniteDimensional ℂ E]

/-- `z ↦ f'(z) v` is continuous on `U`. -/
theorem continuousOn_fderiv_apply {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (v : E) : ContinuousOn (fun z => fderiv ℂ f z v) U := by
  have : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  intro z₀ hz₀
  obtain ⟨R, hR, ε, hε, hsub, hmem⟩ := exists_radius hU hz₀ v
  obtain ⟨M, hM⟩ := (isCompact_closedBall z₀ (2 * ε)).exists_bound_of_continuousOn
    (hf.continuousOn.mono hsub)
  have hpath : ∀ z ∈ ball z₀ ε, ∀ θ : ℝ, z + circleMap 0 R θ • v ∈ closedBall z₀ (2 * ε) :=
    fun z hz θ => hmem z hz _ (norm_circleMap_le hR θ)
  have hcont : ContinuousAt
      (fun z => ∫ θ in (0 : ℝ)..2 * π, kernel R θ • f (z + circleMap 0 R θ • v)) z₀ := by
    refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => R⁻¹ * M)
      ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [ball_mem_nhds z₀ hε] with z hz
      refine ((continuous_kernel hR.ne').smul ?_).aestronglyMeasurable
      exact hf.continuousOn.comp_continuous (by fun_prop) fun θ => hsub (hpath z hz θ)
    · filter_upwards [ball_mem_nhds z₀ hε] with z hz
      refine Eventually.of_forall fun θ _ => ?_
      rw [norm_smul, norm_kernel hR]
      exact mul_le_mul_of_nonneg_left (hM _ (hpath z hz θ)) (inv_nonneg.2 hR.le)
    · refine Eventually.of_forall fun θ _ => ?_
      refine continuousAt_const.smul ?_
      have h1 : ContinuousAt f (z₀ + circleMap 0 R θ • v) :=
        hf.continuousOn.continuousAt (hU.mem_nhds (hsub (hpath z₀ (mem_ball_self hε) θ)))
      exact h1.comp (f := fun z => z + circleMap 0 R θ • v) (by fun_prop)
  refine ((hcont.const_smul ((2 * π * I)⁻¹)).congr ?_).continuousWithinAt
  filter_upwards [ball_mem_nhds z₀ hε] with z hz
  exact (fderiv_apply_eq_integral hU hf hR fun t ht => hsub (hmem z hz t ht)).symm

/-- The derivative of a function complex differentiable on an open set `U` is continuous on
`U`. -/
theorem continuousOn_fderiv {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContinuousOn (fderiv ℂ f) U :=
  continuousOn_clm_apply.2 fun v => continuousOn_fderiv_apply hU hf v

/-- `z ↦ f'(z) v` is complex differentiable on `U` (differentiation under the integral sign in
the Cauchy formula). -/
theorem differentiableAt_fderiv_apply {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z₀ : E} (hz₀ : z₀ ∈ U) (v : E) :
    DifferentiableAt ℂ (fun z => fderiv ℂ f z v) z₀ := by
  have : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  obtain ⟨R, hR, ε, hε, hsub, hmem⟩ := exists_radius hU hz₀ v
  obtain ⟨M, hM⟩ := (isCompact_closedBall z₀ (2 * ε)).exists_bound_of_continuousOn
    ((continuousOn_fderiv hU hf).mono hsub)
  have hpath : ∀ z ∈ ball z₀ ε, ∀ θ : ℝ, z + circleMap 0 R θ • v ∈ closedBall z₀ (2 * ε) :=
    fun z hz θ => hmem z hz _ (norm_circleMap_le hR θ)
  have hderiv := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (a := 0) (b := 2 * π)
    (F := fun z θ => kernel R θ • f (z + circleMap 0 R θ • v))
    (F' := fun z θ => kernel R θ • fderiv ℂ f (z + circleMap 0 R θ • v))
    (x₀ := z₀) (bound := fun _ => R⁻¹ * M) (ball_mem_nhds z₀ hε) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_
  · refine ((hderiv.const_smul ((2 * π * I)⁻¹)).differentiableAt).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds z₀ hε] with z hz
    exact fderiv_apply_eq_integral hU hf hR fun t ht => hsub (hmem z hz t ht)
  · filter_upwards [ball_mem_nhds z₀ hε] with z hz
    refine ((continuous_kernel hR.ne').smul ?_).aestronglyMeasurable
    exact hf.continuousOn.comp_continuous (by fun_prop) fun θ => hsub (hpath z hz θ)
  · refine ((continuous_kernel hR.ne').smul ?_).intervalIntegrable _ _
    exact hf.continuousOn.comp_continuous (by fun_prop) fun θ =>
      hsub (hpath z₀ (mem_ball_self hε) θ)
  · refine ((continuous_kernel hR.ne').smul ?_).aestronglyMeasurable
    exact (continuousOn_fderiv hU hf).comp_continuous (by fun_prop) fun θ =>
      hsub (hpath z₀ (mem_ball_self hε) θ)
  · refine Eventually.of_forall fun θ _ z hz => ?_
    rw [norm_smul, norm_kernel hR]
    exact mul_le_mul_of_nonneg_left (hM _ (hpath z hz θ)) (inv_nonneg.2 hR.le)
  · refine Eventually.of_forall fun θ _ z hz => ?_
    have hfd : HasFDerivAt f (fderiv ℂ f (z + circleMap 0 R θ • v))
        (z + circleMap 0 R θ • v) :=
      (hf.differentiableAt (hU.mem_nhds (hsub (hpath z hz θ)))).hasFDerivAt
    have h2 := hfd.comp z ((hasFDerivAt_id z).add_const (circleMap 0 R θ • v))
    simp only [ContinuousLinearMap.comp_id] at h2
    exact h2.const_smul (kernel R θ)

/-- The derivative of a function complex differentiable on an open set `U` of a
finite-dimensional space is complex differentiable on `U`. -/
theorem differentiableOn_fderiv {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : DifferentiableOn ℂ (fderiv ℂ f) U := by
  intro z hz
  let b := Module.finBasis ℂ E
  let c : Fin (Module.finrank ℂ E) → StrongDual ℂ E := fun k =>
    LinearMap.toContinuousLinearMap (b.coord k)
  have hrepr : fderiv ℂ f =
      fun z => ∑ k, ContinuousLinearMap.smulRightL ℂ E F (c k) (fderiv ℂ f z (b k)) := by
    funext z
    ext x
    simp [c]
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul]
  rw [hrepr]
  refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.fun_sum fun k _ => ?_)
  exact (ContinuousLinearMap.smulRightL ℂ E F (c k)).differentiableAt.comp z
    (differentiableAt_fderiv_apply hU hf hz (b k))

end Langlands.Analysis.HolomorphicContDiff

namespace Langlands.Analysis

open HolomorphicContDiff

universe u

/-- **Holomorphic functions of several variables are smooth.** A function on a
finite-dimensional complex normed space that is complex differentiable on an open set `U` is
infinitely complex differentiable on `U`. -/
theorem contDiffOn_of_differentiableOn {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ ∞ f U := by
  rw [contDiffOn_infty]
  intro n
  induction n generalizing F with
  | zero => exact contDiffOn_zero.2 hf.continuousOn
  | succ n ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨hf, by simp, ih (differentiableOn_fderiv hU hf)⟩

/-- A function holomorphic on an open set `D ⊆ ℂᵐ`, composed with a real-linear map
`A : ℝⁿ → ℂᵐ` whose values lie in `D`, is a smooth function of the real variables. -/
theorem contDiff_comp_of_differentiableOn {m n : ℕ} {f : (Fin m → ℂ) → ℂ}
    {D : Set (Fin m → ℂ)} (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (A : (Fin n → ℝ) →L[ℝ] (Fin m → ℂ)) (hA : ∀ x, A x ∈ D) :
    ContDiff ℝ ∞ fun x => f (A x) :=
  ((contDiffOn_of_differentiableOn hD hf).restrict_scalars ℝ).comp_contDiff A.contDiff hA

end Langlands.Analysis
