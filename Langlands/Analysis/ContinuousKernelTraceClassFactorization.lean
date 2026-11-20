import Langlands.Analysis.ContinuousKernelHilbertSchmidt
import Langlands.Analysis.HilbertSchmidtProductTraceClassProof
import Mathlib.MeasureTheory.Integral.Prod

/-! # A trace-class criterion by factorization through continuous compact kernels -/

noncomputable section

open MeasureTheory Filter

set_option autoImplicit false

namespace Langlands.Analysis.OperatorIdeals

variable {X Z : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Z] [CompactSpace Z]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Z] [BorelSpace Z]
  (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure Z) [IsFiniteMeasure ν]
  (P : C(X × X, ℂ)) (A : C(X × Z, ℂ)) (B : C(Z × X, ℂ))

local notation "U" => ContinuousMap.toLp (E := ℂ) 2 μ ℂ
local notation "V" => ContinuousMap.toLp (E := ℂ) 2 ν ℂ

/-- Compose the two continuous kernel operators through the intermediate `L²` space. -/
def continuousKernelComposition : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  ((U).comp (continuousKernelProfile ν A)).comp ((V).comp (continuousKernelProfile μ B))

include μ ν in
private theorem integrable_kernel_product (v : Lp ℂ 2 μ) (x : X) :
    Integrable (fun zy : Z × X => A (x, zy.1) * B zy * v zy.2) (ν.prod μ) := by
  have hv : Integrable (fun y => v y) μ := memLp_one_iff_integrable.mp ((Lp.memLp v).mono_exponent one_le_two)
  have hc : Continuous (fun zy : Z × X => A (x, zy.1) * B zy) :=
    (A.continuous.comp (continuous_const.prodMk continuous_fst)).mul B.continuous
  apply ((hv.norm.comp_snd ν).const_mul (‖A‖ * ‖B‖)).mono
    (hc.aestronglyMeasurable.mul hv.aestronglyMeasurable.comp_snd)
  refine Eventually.of_forall fun zy => ?_
  have hK : ‖A (x, zy.1)‖ * ‖B zy‖ ≤ ‖A‖ * ‖B‖ :=
    mul_le_mul (A.norm_coe_le_norm _) (B.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  simpa only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_norm] using
    mul_le_mul_of_nonneg_right hK (norm_nonneg (v zy.2))

/-- Integrating the product of two compact kernels computes composition on `L²`. -/
theorem continuousKernelOperator_eq_comp
    (hP : ∀ x y, P (x, y) = ∫ z, A (x, z) * B (z, y) ∂ν) :
    (U).comp (continuousKernelProfile μ P) = continuousKernelComposition μ ν A B := by
  apply ContinuousLinearMap.ext
  intro v
  let b := continuousKernelProfile μ B v
  change U (continuousKernelProfile μ P v) = U (continuousKernelProfile ν A (V b))
  congr 1
  ext x
  rw [continuousKernelProfile_apply, continuousKernelProfile_apply]
  calc
    _ = ∫ y, (∫ z, A (x, z) * B (z, y) ∂ν) * v y ∂μ :=
      integral_congr_ae (Eventually.of_forall fun y => congrArg (· * v y) (hP x y))
    _ = ∫ y, (∫ z, A (x, z) * B (z, y) * v y ∂ν) ∂μ := by simp only [integral_mul_const]
    _ = ∫ z, (∫ y, A (x, z) * B (z, y) * v y ∂μ) ∂ν :=
      (integral_integral_swap (integrable_kernel_product μ ν A B v x)).symm
    _ = ∫ z, A (x, z) * b z ∂ν := by
      simp only [mul_assoc, integral_const_mul, b, continuousKernelProfile_apply]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℂ) b] with z hz
      rw [hz]

/-- An `L²` kernel endomorphism that factors through two continuous compact kernels is trace class. -/
theorem isTraceClass_continuousKernelOperator_of_factorization
    (hP : ∀ x y, P (x, y) = ∫ z, A (x, z) * B (z, y) ∂ν) :
    IsTraceClass ((U).comp (continuousKernelProfile μ P)) := by
  rw [continuousKernelOperator_eq_comp μ ν P A B hP]
  exact hilbertSchmidtProductTraceClass (Lp ℂ 2 μ) (Lp ℂ 2 ν) _ _
    (isHilbertSchmidt_continuousKernelProfile μ B ν)
    (isHilbertSchmidt_continuousKernelProfile ν A μ)

end Langlands.Analysis.OperatorIdeals
