import Langlands.Global.AdelicRestrictionSplitCentre

/-! # Rational split centre of the restriction versus the split component of the group -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme

/-- For every number field and affine locally finite-type group scheme `G`, a split component
of the Weil restriction over `ℚ` and a split component of `G` over `F` give the same positive
real subgroup of the actual adelic points. -/
def ComparisonStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
    (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G),
    IsSplitComponent j → IsSplitComponent i →
      subgroup F G S j = PositiveRealTorus.imageSubgroup F T G i

end Langlands.Global.RestrictionSplitCentre
