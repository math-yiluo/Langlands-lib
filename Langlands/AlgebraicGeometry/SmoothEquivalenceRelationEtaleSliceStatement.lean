import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasRelation

/-! # Etale slices of smooth equivalence relations on schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace.AtlasRelation

/-- Every equivalence relation `(t, s) : R ⟶ U × U` of schemes with smooth projections has
an etale slice: a scheme `U'` with a morphism `g : U' ⟶ U` locally of finite type such that
`h = s ∘ pr₂ : U' ×_{g, U, t} R ⟶ U` is etale and surjective. -/
def SmoothEquivalenceRelationEtaleSliceStatement : Prop :=
  ∀ (U R : Scheme.{u}) (t s : R ⟶ U), IsEquivRel t s → Smooth t → Smooth s →
    ∃ (U' : Scheme.{u}) (g : U' ⟶ U), LocallyOfFiniteType g ∧
      Etale (pullback.snd g t ≫ s) ∧ Surjective (pullback.snd g t ≫ s)

end Langlands.AlgebraicGeometry
