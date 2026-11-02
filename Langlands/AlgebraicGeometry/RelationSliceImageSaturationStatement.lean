import Langlands.AlgebraicGeometry.SmoothEquivalenceRelationEtaleSliceStatement

/-! # Saturation of the image of a scheme slice -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace.AtlasRelation

/-- The associated image of a slice contains the original image and is invariant under
all arrows of the equivalence relation on underlying scheme points. -/
def RelationSliceImageSaturationStatement : Prop :=
  ∀ (U R : Scheme.{u}) (t s : R ⟶ U), IsEquivRel t s →
    ∀ (V : Scheme.{u}) (g : V ⟶ U),
      Set.range g ⊆ Set.range (pullback.snd g t ≫ s) ∧
        ∀ r : R, t r ∈ Set.range (pullback.snd g t ≫ s) ↔
          s r ∈ Set.range (pullback.snd g t ≫ s)

end Langlands.AlgebraicGeometry
