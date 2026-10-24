import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Unitary.Basic

/-!
# Analytic properties of universe lifts

Specializations of the existing representation-equivalence transport laws.
The final example checks the carrier universe required by the p-adic
classification interfaces, without assuming or proving a classification.
-/

namespace Langlands

universe uX uG uV uF

variable {G : Type uG} [Group G] {V : Type uV}
  [AddCommGroup V] [Module ℂ V]

theorem isUnitarizable_universeLift_iff (ρ : Representation ℂ G V) :
    IsUnitarizable (universeLiftRepresentation.{uX} ρ) ↔ IsUnitarizable ρ :=
  (isUnitarizable_iff_of_equiv (universeLiftEquiv ρ)).symm

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ}

theorem isTempered_universeLift_iff
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    T.IsTempered (universeLiftRepresentation.{uX} ρ) ↔ T.IsTempered ρ :=
  (T.isTempered_iff_of_equiv (universeLiftEquiv ρ)).symm

theorem isSquareIntegrable_universeLift_iff
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    T.IsSquareIntegrable (universeLiftRepresentation.{uX} ρ) ↔
      T.IsSquareIntegrable ρ :=
  (T.isSquareIntegrable_iff_of_equiv (universeLiftEquiv ρ)).symm

/-- The field and source-carrier universes are independent. Lifting by `uF`
gives exactly the carrier universe used by the classification targets. -/
example :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      ∃ B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        Nonempty (A.representation.Equiv B.representation) ∧
        (B.IsIrreducible ↔ A.IsIrreducible) ∧
        (B.IsAdmissible ↔ A.IsAdmissible) ∧
        (IsUnitarizable B.representation ↔ IsUnitarizable A.representation) ∧
        (T.IsTempered B.representation ↔ T.IsTempered A.representation) ∧
        (T.IsSquareIntegrable B.representation ↔
          T.IsSquareIntegrable A.representation) := by
  let := T.topology
  intro A
  exact ⟨SmoothRep.universeLift.{uF} A, ⟨A.universeLiftEquiv⟩,
    A.isIrreducible_universeLift_iff, A.isAdmissible_universeLift_iff,
    isUnitarizable_universeLift_iff A.representation,
    T.isTempered_universeLift_iff A.representation,
    T.isSquareIntegrable_universeLift_iff A.representation⟩

end PadicField.TopologicalData
end Langlands
