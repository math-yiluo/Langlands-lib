import Langlands.Analysis.HilbertSchmidtEvaluationProof
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Continuous compact kernels as Hilbert–Schmidt operators -/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

set_option autoImplicit false

namespace Langlands.Analysis.OperatorIdeals

universe uX uY

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure Y) [IsFiniteMeasure μ] (P : C(X × Y, ℂ))

private def conjugateKernelRow (x : X) : Lp ℂ 2 μ :=
  ContinuousMap.toLp 2 μ ℂ (star (P.curry x))

/-- A kernel row acts on `L²` by integration against that row. -/
def kernelEvaluation (x : X) : Lp ℂ 2 μ →L[ℂ] ℂ :=
  innerSL ℂ (conjugateKernelRow μ P x)

theorem kernelEvaluation_apply (x : X) (v : Lp ℂ 2 μ) :
    kernelEvaluation μ P x v = ∫ y, P (x, y) * v y ∂μ := by
  change ⟪conjugateKernelRow μ P x, v⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℂ) (star (P.curry x))] with y hy
  change conjugateKernelRow μ P x y = star (P.curry x) y at hy
  rw [hy]
  simp [RCLike.inner_apply, ContinuousMap.star_apply, mul_comm]

private theorem continuous_kernelEvaluation_apply (v : Lp ℂ 2 μ) :
    Continuous (fun x => kernelEvaluation μ P x v) := by
  have h : Continuous (conjugateKernelRow μ P) :=
    (ContinuousMap.toLp 2 μ ℂ).continuous.comp (continuous_star.comp P.curry.continuous)
  exact h.inner continuous_const

variable [CompactSpace X]

private theorem norm_kernelEvaluation_le (x : X) :
    ‖kernelEvaluation μ P x‖ ≤ ‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ‖ * ‖P‖ := by
  have hrow : ‖star (P.curry x)‖ ≤ ‖P‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg P)).mpr
    intro y
    simpa only [ContinuousMap.star_apply, norm_star, ContinuousMap.curry_apply] using
      P.norm_coe_le_norm (x, y)
  calc
    ‖kernelEvaluation μ P x‖ ≤ ‖conjugateKernelRow μ P x‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      exact norm_inner_le_norm (𝕜 := ℂ) (conjugateKernelRow μ P x)
    _ ≤ ‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ‖ * ‖P‖ :=
      ((ContinuousMap.toLp 2 μ ℂ).le_opNorm _).trans (mul_le_mul_of_nonneg_left hrow (norm_nonneg _))

/-- The compact output profile of the integral operator defined by a continuous kernel. -/
def continuousKernelProfile : Lp ℂ 2 μ →L[ℂ] C(X, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun x => kernelEvaluation μ P x v, continuous_kernelEvaluation_apply μ P v⟩
      map_add' := fun v w => ContinuousMap.ext fun x => map_add (kernelEvaluation μ P x) v w
      map_smul' := fun c v => ContinuousMap.ext fun x => map_smul (kernelEvaluation μ P x) c v }
    (‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ‖ * ‖P‖) (by
      intro v
      apply (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (norm_nonneg v))).mpr
      intro x
      exact ((kernelEvaluation μ P x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (norm_kernelEvaluation_le μ P x) (norm_nonneg v)))

@[simp]
theorem continuousKernelProfile_apply (v : Lp ℂ 2 μ) (x : X) :
    continuousKernelProfile μ P v x = ∫ y, P (x, y) * v y ∂μ :=
  kernelEvaluation_apply μ P x v

variable [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

/-- A continuous kernel on compact spaces with finite measures gives a Hilbert–Schmidt operator
between the corresponding complex `L²` spaces. -/
theorem isHilbertSchmidt_continuousKernelProfile :
    IsHilbertSchmidt ((ContinuousMap.toLp 2 ν ℂ).comp (continuousKernelProfile μ P)) := by
  let A := (ContinuousMap.toLp 2 ν ℂ).comp (continuousKernelProfile μ P)
  have hrep (v : Lp ℂ 2 μ) : (A v : X → ℂ) =ᵐ[ν] fun x => kernelEvaluation μ P x v :=
    ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℂ) (continuousKernelProfile μ P v)
  exact (hilbertSchmidtUniformEvaluation.{uY, uX, 0} (Lp ℂ 2 μ) X ν A (kernelEvaluation μ P)
    (‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ‖ * ‖P‖) (by positivity) hrep
    (Filter.Eventually.of_forall (norm_kernelEvaluation_le μ P))).1

end Langlands.Analysis.OperatorIdeals
