import Langlands.Representation.Unitary.IntegratedOperator
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

universe uX uG

namespace Langlands.Analysis

open MeasureTheory

/-- The Bochner-integrated translation action on an actual `L²` space is
represented almost everywhere by the pointwise weighted integral of a
representative along the original measure-preserving right action. -/
def IntegratedTranslationPointwiseStatement : Prop :=
  ∀ (X : Type uX) [MeasurableSpace X] (μX : Measure X) [SigmaFinite μX]
    (G : Type uG) [Group G] [MeasurableSpace G] (μ : Measure G) [SigmaFinite μ]
    (act : X → G → X),
    Measurable (fun p : X × G => act p.1 p.2) →
    (∀ g : G, MeasurePreserving (fun x => act x g) μX μX) →
    ∀ (π : G →* (Lp ℂ 2 μX →L[ℂ] Lp ℂ 2 μX))
      (hπnorm : ∀ (g : G) (φ : Lp ℂ 2 μX), ‖π g φ‖ = ‖φ‖)
      (hπmeas : ∀ φ : Lp ℂ 2 μX, AEStronglyMeasurable (fun g => π g φ) μ),
      (∀ (g : G) (φ : Lp ℂ 2 μX), (π g φ : X → ℂ) =ᵐ[μX] fun x => φ (act x g)) →
      ∀ (f : G → ℂ) (hf : Integrable f μ) (φ : Lp ℂ 2 μX),
        (∀ᵐ x ∂μX, Integrable (fun g => f g * φ (act x g)) μ) ∧
        (integratedIsometricAction μ π hπnorm hπmeas f hf φ : X → ℂ) =ᵐ[μX]
          fun x => ∫ g, f g * φ (act x g) ∂μ

end Langlands.Analysis
