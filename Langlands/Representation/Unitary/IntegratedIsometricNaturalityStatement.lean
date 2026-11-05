import Langlands.Representation.Unitary.IntegratedOperator

noncomputable section

namespace Langlands.Analysis

open MeasureTheory

universe uG uE

/-- Preservation and actual intertwiner compatibility of the Bochner operator. -/
def IntegratedIsometricNaturalityStatement : Prop :=
  ∀ {G : Type uG} [Group G] [MeasurableSpace G]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) (π : G →* (E →L[ℂ] E))
    (hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖)
    (hπmeas : ∀ x : E, AEStronglyMeasurable (fun g => π g x) μ)
    (f : G → ℂ) (hf : Integrable f μ),
    let T := integratedIsometricAction μ π hπnorm hπmeas f hf
    ∀ (P : Submodule ℂ E) (_hPc : IsClosed (P : Set E))
      (hPi : ∀ (g : G) (x : E), x ∈ P → π g x ∈ P),
      ∃ hTP : ∀ (x : E), x ∈ P → T x ∈ P,
        ∀ (Q : Submodule ℂ E) (U : P ≃ₗᵢ[ℂ] Q),
          (∀ (g : G) (x : P),
            (U ⟨π g x, hPi g x x.property⟩ : E) = π g (U x : E)) →
          ∀ x : P, (U ⟨T x, hTP x x.property⟩ : E) = T (U x : E)

end Langlands.Analysis
