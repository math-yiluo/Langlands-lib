import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.LinearIsometry

noncomputable section

namespace Langlands.Analysis

open MeasureTheory

universe uG uE

variable {G : Type uG} [Group G] [MeasurableSpace G]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (μ : Measure G) (π : G →* (E →L[ℂ] E))
variable (hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖)
variable (hπmeas : ∀ x : E, AEStronglyMeasurable (fun g => π g x) μ)
variable (f : G → ℂ) (hf : Integrable f μ)

include hπnorm hπmeas hf

/-- The weighted orbit is genuinely Bochner integrable. -/
theorem isometricActionIntegrand_integrable (x : E) :
    Integrable (fun g => f g • π g x) μ := by
  apply (hf.norm.mul_const ‖x‖).mono' (hf.aestronglyMeasurable.smul (hπmeas x))
  exact Filter.Eventually.of_forall (fun g => by
    change ‖f g • π g x‖ ≤ ‖f g‖ * ‖x‖
    rw [norm_smul, hπnorm])

/-- Vectorwise Bochner integration of a norm-preserving action is linear. -/
def integratedIsometricActionLinear : E →ₗ[ℂ] E where
  toFun x := ∫ g, f g • π g x ∂μ
  map_add' x y := by
    simp only [map_add, smul_add]
    exact integral_add (isometricActionIntegrand_integrable μ π hπnorm hπmeas f hf x)
      (isometricActionIntegrand_integrable μ π hπnorm hπmeas f hf y)
  map_smul' c x := by
    simp only [map_smul, smul_comm (f _) c]
    exact integral_smul c (fun g => f g • π g x)

/-- The scalar L1 norm bounds the integrated operator on every vector. -/
theorem integratedIsometricActionLinear_bound (x : E) :
    ‖integratedIsometricActionLinear μ π hπnorm hπmeas f hf x‖ ≤
      (∫ g, ‖f g‖ ∂μ) * ‖x‖ := by
  change ‖∫ g, f g • π g x ∂μ‖ ≤ _
  calc
    ‖∫ g, f g • π g x ∂μ‖ ≤ ∫ g, ‖f g‖ * ‖x‖ ∂μ :=
      norm_integral_le_of_norm_le (hf.norm.mul_const ‖x‖)
        (Filter.Eventually.of_forall (fun g => by rw [norm_smul, hπnorm]))
    _ = (∫ g, ‖f g‖ ∂μ) * ‖x‖ := integral_mul_const ‖x‖ _

/-- The actual bounded operator defined by the weighted orbit integral. -/
def integratedIsometricAction [CompleteSpace E] : E →L[ℂ] E :=
  (integratedIsometricActionLinear μ π hπnorm hπmeas f hf).mkContinuous
    (∫ g, ‖f g‖ ∂μ) (integratedIsometricActionLinear_bound μ π hπnorm hπmeas f hf)

variable [CompleteSpace E]

@[simp]
theorem integratedIsometricAction_apply (x : E) :
    integratedIsometricAction μ π hπnorm hπmeas f hf x = ∫ g, f g • π g x ∂μ := rfl

/-- The constructor's explicit operator norm bound. -/
theorem integratedIsometricAction_norm_le :
    ‖integratedIsometricAction μ π hπnorm hπmeas f hf‖ ≤ ∫ g, ‖f g‖ ∂μ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg (fun _ => norm_nonneg _))
    (integratedIsometricActionLinear_bound μ π hπnorm hπmeas f hf)

end Langlands.Analysis
