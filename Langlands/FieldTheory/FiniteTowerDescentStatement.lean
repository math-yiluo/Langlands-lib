import Mathlib.FieldTheory.LinearDisjoint

/-! # Compatible finite-tower descent along a directed union of fields -/

namespace Langlands.FieldTheory

universe u v

/-- A finite separable extension followed by a finite Galois extension descends
simultaneously to one stage of a directed union, with the literal tower maps,
all three degrees, and prescribed finite subsets retained by the same witnesses. -/
def FiniteTowerDirectedUnionDescent : Prop :=
  ∀ (U E L : Type u) [Field U] [Field E] [Field L]
    [Algebra U E] [FiniteDimensional U E] [Algebra.IsSeparable U E]
    [Algebra E L] [FiniteDimensional E L] [IsGalois E L],
    letI : Algebra U L := ((algebraMap E L).comp (algebraMap U E)).toAlgebra
    letI : IsScalarTower U E L := IsScalarTower.of_algebraMap_eq' rfl
    ∀ (I : Type v) [Nonempty I] (A : I → Subfield U),
      Directed (· ≤ ·) A →
      (∀ x : U, ∃ i : I, x ∈ A i) →
      ∀ (i₀ : I) (sE : Finset E) (sL : Finset L),
        ∃ i : I, A i₀ ≤ A i ∧
          letI : Algebra (A i) U := Algebra.ofSubsemiring (A i)
          letI : Algebra (A i) E := Algebra.ofSubsemiring (A i)
          letI : Algebra (A i) L := Algebra.ofSubsemiring (A i)
          letI : IsScalarTower (A i) U E :=
            IsScalarTower.of_algebraMap_eq' rfl
          letI : IsScalarTower (A i) U L :=
            IsScalarTower.of_algebraMap_eq' rfl
          letI : IsScalarTower (A i) E L :=
            IsScalarTower.of_algebraMap_eq' rfl
          ∃ B : IntermediateField (A i) E,
            letI : Algebra B L := Algebra.ofSubsemiring B
            letI : IsScalarTower B E L :=
              IsScalarTower.of_algebraMap_eq' rfl
            letI : IsScalarTower (A i) B L := inferInstance
            ∃ C : IntermediateField B L,
              letI : IsScalarTower (A i) C L :=
                IsScalarTower.of_algebraMap_eq' rfl
              FiniteDimensional (A i) B ∧
              Algebra.IsSeparable (A i) B ∧
              Module.finrank (A i) B = Module.finrank U E ∧
              FiniteDimensional B C ∧
              IsGalois B C ∧
              Module.finrank B C = Module.finrank E L ∧
              FiniteDimensional (A i) C ∧
              Module.finrank (A i) C = Module.finrank U L ∧
              B.LinearDisjoint U ∧
              IntermediateField.adjoin U (B : Set E) = ⊤ ∧
              (C.restrictScalars (A i)).LinearDisjoint U ∧
              IntermediateField.adjoin U (C : Set L) = ⊤ ∧
              C.LinearDisjoint E ∧
              IntermediateField.adjoin E (C : Set L) = ⊤ ∧
              (∀ x ∈ sE, x ∈ B) ∧
              (∀ x ∈ sL, x ∈ C) ∧
              (algebraMap C L).comp (algebraMap B C) =
                (algebraMap E L).comp (algebraMap B E)

end Langlands.FieldTheory
