import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Twist.Definitions

/-!
# Unitary twists of analytic coefficients modulo the center

The closed statement retains the actual central quotient, supplied Borel Haar
measure and all smooth-dual coefficient quantifiers of the published predicates.
-/

namespace Langlands

universe uG uV

/-- Twisting by an open-kernel character of norm one preserves and reflects
square-integrability and temperedness for the same Haar measure on the full
central quotient. This is a proposition to be proved separately. -/
def UnitaryTwistModCenterStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace (G ⧸ Subgroup.center G)]
    [BorelSpace (G ⧸ Subgroup.center G)]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ]
    (ρ : Representation ℂ G V) (χ : G →* ℂˣ),
    IsOpen (χ.ker : Set G) →
    (∀ g : G, ‖(χ g : ℂ)‖ = 1) →
    (IsSquareIntegrableModCenter (twist χ ρ) μ ↔
      IsSquareIntegrableModCenter ρ μ) ∧
    (IsTemperedModCenter (twist χ ρ) μ ↔ IsTemperedModCenter ρ μ)

end Langlands
