import Mathlib

/-! # A finite-type-point criterion for global etale slices -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A family of locally finite type slices whose associated maps are etale and meet every
finite type point can be assembled into a single etale surjective slice. -/
def RelationEtaleSliceGlobalizationStatement : Prop :=
  ∀ (U R : Scheme.{u}) (t s : R ⟶ U),
    (∀ x : U, LocallyOfFiniteType (U.fromSpecResidueField x) →
      ∃ (V : Scheme.{u}) (g : V ⟶ U), LocallyOfFiniteType g ∧
        Etale (pullback.snd g t ≫ s) ∧ x ∈ Set.range (pullback.snd g t ≫ s)) →
    ∃ (V : Scheme.{u}) (g : V ⟶ U), LocallyOfFiniteType g ∧
      Etale (pullback.snd g t ≫ s) ∧ Surjective (pullback.snd g t ≫ s)

end Langlands.AlgebraicGeometry
