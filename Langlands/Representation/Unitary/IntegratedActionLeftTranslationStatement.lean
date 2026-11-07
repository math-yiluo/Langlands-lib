import Langlands.Representation.Unitary.IntegratedOperator
import Mathlib.MeasureTheory.Group.Integral

noncomputable section

universe uG uE

namespace Langlands.Analysis

open MeasureTheory

/-- Left translation of an actual integrated isometric action equals integration
against the correspondingly translated scalar weight. -/
def IntegratedActionLeftTranslationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [MeasurableSpace G] [MeasurableMul G]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (π : G →* (E →L[ℂ] E))
    (hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖)
    (hπmeas : ∀ x : E, AEStronglyMeasurable (fun g => π g x) μ)
    (f : G → ℂ) (hf : Integrable f μ) (x : E) (p : G),
    Integrable (fun y => f (p⁻¹ * y) • π y x) μ ∧
      π p (integratedIsometricAction μ π hπnorm hπmeas f hf x) =
        ∫ y, f (p⁻¹ * y) • π y x ∂μ

end Langlands.Analysis
