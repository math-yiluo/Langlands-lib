import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasRelation

/-! # Etale propagation and shrinking for a relation slice -/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace.AtlasRelation

/-- An etale stalk at a section point of a relation slice extends, after
shrinking the slicing scheme, to an etale slice map. -/
def RelationSliceEtalePropagationStatement : Prop :=
  ∀ (U R V : Scheme.{u}) (t s : R ⟶ U), IsEquivRel t s →
    ∀ (g : V ⟶ U), Flat s → LocallyOfFinitePresentation (pullback.snd g t ≫ s) →
      ∀ (σ : V ⟶ pullback g t), σ ≫ pullback.fst g t = 𝟙 V →
        ∀ (v : V), ((pullback.snd g t ≫ s).stalkMap (σ v)).hom.FormallyEtale →
          ∃ W : V.Opens, v ∈ W ∧ Etale (pullback.snd (W.ι ≫ g) t ≫ s)

end Langlands.AlgebraicGeometry
