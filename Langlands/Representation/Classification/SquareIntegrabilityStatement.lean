import Langlands.LocalField.Definitions
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Representation.Twist.Definitions
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Square-integrability prerequisites for actual general linear groups

This family records independence of Haar normalization, unitary character
twisting, smooth contragredients, and Casselman's single-coefficient criterion.
It does not define square-integrability by an exponent criterion.
-/

namespace Langlands

universe uF uV

/-- Analytic prerequisites for square-integrability modulo the actual center,
over every finite extension of every p-adic field. -/
def GLSquareIntegrabilityPrerequisitesStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopology
    letI : IsTopologicalRing F.Carrier :=
      IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
    ∀ (n : ℕ), 0 < n →
      let G := Matrix.GeneralLinearGroup (Fin n) F.Carrier
      let Q := G ⧸ Subgroup.center G
      ∀ [MeasurableSpace Q] [BorelSpace Q]
        (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ G V),
        IsAdmissible ρ →
        (∀ (ν : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure ν],
          IsSquareIntegrableModCenter ρ μ ↔ IsSquareIntegrableModCenter ρ ν) ∧
        (∀ η : G →* ℂˣ, IsOpen (η.ker : Set G) →
          (∀ g : G, ‖(η g : ℂ)‖ = 1) →
          (IsSquareIntegrableModCenter (twist η ρ) μ ↔
            IsSquareIntegrableModCenter ρ μ)) ∧
        (IsSquareIntegrableModCenter (smoothContragredient ρ) μ ↔
          IsSquareIntegrableModCenter ρ μ) ∧
        (Representation.IsIrreducible ρ →
          ∀ c : UnitaryCentralCharacter ρ,
            IsSquareIntegrableModCenter ρ μ ↔
              ∃ (v : V) (ℓ : SmoothDual ρ),
                v ≠ 0 ∧ ℓ ≠ 0 ∧
                  MeasureTheory.MemLp (c.coefficientNorm ℓ v) 2 μ)

end Langlands
