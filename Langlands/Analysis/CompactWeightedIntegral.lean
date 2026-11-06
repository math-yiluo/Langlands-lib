import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

universe uX uE

namespace Langlands.Analysis

open MeasureTheory

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (μ : Measure X) [IsFiniteMeasure μ] (w : C(X, E))

/-- Every continuous scalar weight has an absolutely integrable weighted orbit. -/
theorem compactWeightedIntegral_integrable (f : C(X, ℂ)) :
    Integrable (fun x => f x • w x) μ :=
  (f.continuous.smul w.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Scalar integration against the fixed continuous vector-valued weight. -/
def compactWeightedIntegralLinear [CompleteSpace E] : C(X, ℂ) →ₗ[ℂ] E where
  toFun f := ∫ x, f x • w x ∂μ
  map_add' f g := by
    change (∫ x, (f x + g x) • w x ∂μ) = _
    simp only [add_smul]
    exact integral_add (compactWeightedIntegral_integrable μ w f)
      (compactWeightedIntegral_integrable μ w g)
  map_smul' c f := by
    change (∫ x, (c * f x) • w x ∂μ) = _
    simp only [mul_smul]
    exact integral_smul c (fun x => f x • w x)

variable [CompleteSpace E]

/-- The L1 norm of the fixed vector-valued weight is an operator bound. -/
theorem compactWeightedIntegralLinear_bound (f : C(X, ℂ)) :
    ‖compactWeightedIntegralLinear μ w f‖ ≤ (∫ x, ‖w x‖ ∂μ) * ‖f‖ := by
  have hw : Integrable (fun x => ‖w x‖) μ :=
    (w.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).norm
  change ‖∫ x, f x • w x ∂μ‖ ≤ _
  calc
    ‖∫ x, f x • w x ∂μ‖ ≤ ∫ x, ‖f‖ * ‖w x‖ ∂μ :=
      norm_integral_le_of_norm_le (hw.const_mul ‖f‖)
        (Filter.Eventually.of_forall fun x => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x) (norm_nonneg _))
    _ = (∫ x, ‖w x‖ ∂μ) * ‖f‖ := by
      rw [integral_const_mul, mul_comm]

/-- The actual bounded map from scalar kernels to vector-valued integrals. -/
def compactWeightedIntegral : C(X, ℂ) →L[ℂ] E :=
  (compactWeightedIntegralLinear μ w).mkContinuous (∫ x, ‖w x‖ ∂μ)
    (compactWeightedIntegralLinear_bound μ w)

@[simp]
theorem compactWeightedIntegral_apply (f : C(X, ℂ)) :
    compactWeightedIntegral μ w f = ∫ x, f x • w x ∂μ := rfl

/-- The constructor retains the explicit L1 bound on its norm. -/
theorem compactWeightedIntegral_norm_le :
    ‖compactWeightedIntegral μ w‖ ≤ ∫ x, ‖w x‖ ∂μ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ => norm_nonneg _)
    (compactWeightedIntegralLinear_bound μ w)

end Langlands.Analysis
