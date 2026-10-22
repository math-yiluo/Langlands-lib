import Mathlib.FieldTheory.LinearDisjoint

/-! # Finite-extension descent along a directed union of fields -/

namespace Langlands.FieldTheory

universe u v

/-- A finite extension of a directed union descends to a finite extension of
one stage, retaining a prescribed initial stage and finitely many elements.
The same witness preserves separability and Galoisness when applicable. -/
def FiniteExtensionDirectedUnionDescent : Prop :=
  ∀ (L M : Type u) [Field L] [Field M] [Algebra L M]
    [FiniteDimensional L M] (I : Type v) [Nonempty I]
    (A : I → Subfield L),
    Directed (· ≤ ·) A →
    (∀ x : L, ∃ i : I, x ∈ A i) →
    ∀ (i₀ : I) (s : Finset M),
      ∃ i : I, A i₀ ≤ A i ∧
        letI : Algebra (A i) L := Algebra.ofSubsemiring (A i)
        letI : Algebra (A i) M := Algebra.ofSubsemiring (A i)
        letI : IsScalarTower (A i) L M :=
          IsScalarTower.of_algebraMap_eq' rfl
        ∃ B : IntermediateField (A i) M,
          letI : IsScalarTower (A i) B M := inferInstance
          FiniteDimensional (A i) B ∧
          Module.finrank (A i) B = Module.finrank L M ∧
          B.LinearDisjoint L ∧
          IntermediateField.adjoin L (B : Set M) = ⊤ ∧
          (∀ x ∈ s, x ∈ B) ∧
          (Algebra.IsSeparable L M → Algebra.IsSeparable (A i) B) ∧
          (IsGalois L M → IsGalois (A i) B)

end Langlands.FieldTheory
