import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.LocalField.RelativeIntegers
import Mathlib.FieldTheory.LinearDisjoint

/-! # Finite totally ramified and unramified composita -/

namespace Langlands.LocalClassField

universe u

/-- A finite totally ramified Galois extension retains its degree and
ramification after any finite unramified base extension in the same closure.
The residue map, order comparison, and norm comparison use the actual
inclusions into the compositum. -/
def TotalUnramifiedCompositum : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E K' : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier E.field],
    (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
        Module.finrank F.Carrier E.field *
          F.canonicalTopologicalData.ramificationIndex →
    (K'.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
        F.canonicalTopologicalData.ramificationIndex →
    E.field.LinearDisjoint K'.field ∧
    ∃ M : FiniteIntermediateExtension F.Carrier,
      M.field = E.field ⊔ K'.field ∧
      ∃ hE : E.field ≤ M.field, ∃ hK : K'.field ≤ M.field,
        letI := (E.asPadicField (p := p)).algebra
        letI := (K'.asPadicField (p := p)).algebra
        letI := (M.asPadicField (p := p)).algebra
        letI : Algebra E.field M.field := (IntermediateField.inclusion hE).toAlgebra
        letI : Algebra K'.field M.field := (IntermediateField.inclusion hK).toAlgebra
        letI : IsScalarTower F.Carrier E.field M.field :=
          IsScalarTower.of_algebraMap_eq' rfl
        letI : IsScalarTower F.Carrier K'.field M.field :=
          IsScalarTower.of_algebraMap_eq' rfl
        letI : IsScalarTower (Padic p) E.field M.field :=
          IsScalarTower.of_algebraMap_eq' rfl
        letI : IsScalarTower (Padic p) K'.field M.field :=
          IsScalarTower.of_algebraMap_eq' rfl
        letI : FiniteDimensional K'.field M.field :=
          FiniteDimensional.right F.Carrier K'.field M.field
        Module.finrank K'.field M.field = Module.finrank F.Carrier E.field ∧
        (M.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
          (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ∧
        IsGalois K'.field M.field ∧
        Function.Bijective (PadicField.TopologicalData.relativeResidueMap
          (F := K'.asPadicField (p := p)) (E := M.asPadicField (p := p))
          (K'.asPadicField (p := p)).canonicalTopologicalData
          (M.asPadicField (p := p)).canonicalTopologicalData) ∧
        (∀ z : E.field,
          (M.asPadicField (p := p)).canonicalTopologicalData.ord
              (IntermediateField.inclusion hE z) =
            (E.asPadicField (p := p)).canonicalTopologicalData.ord z) ∧
        (∀ z : E.field,
          Algebra.norm K'.field (IntermediateField.inclusion hE z) =
            algebraMap F.Carrier K'.field (Algebra.norm F.Carrier z))

end Langlands.LocalClassField
