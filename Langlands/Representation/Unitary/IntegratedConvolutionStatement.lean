import Langlands.Representation.Unitary.IntegratedOperator
import Mathlib.MeasureTheory.Group.Arithmetic

noncomputable section

universe uG uE

namespace Langlands.Analysis

open MeasureTheory

/-- For a left-invariant s-finite measure on a measurable group, the integrated
action of a norm-preserving representation sends the convolution
`g ↦ ∫ a, f₁ a * f₂ (a⁻¹ * g)` of two integrable weights, which is itself
integrable, to the composition of the two integrated operators. -/
def IntegratedActionConvolutionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (π : G →* (E →L[ℂ] E))
    (hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖)
    (hπmeas : ∀ x : E, AEStronglyMeasurable (fun g => π g x) μ)
    (f₁ f₂ : G → ℂ) (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ),
    ∃ h : Integrable (fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μ) μ,
      integratedIsometricAction μ π hπnorm hπmeas
          (fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μ) h =
        (integratedIsometricAction μ π hπnorm hπmeas f₁ h₁).comp
          (integratedIsometricAction μ π hπnorm hπmeas f₂ h₂)

end Langlands.Analysis
