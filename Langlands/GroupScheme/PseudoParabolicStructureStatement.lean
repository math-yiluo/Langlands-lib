import Langlands.GroupScheme.PseudoParabolic

/-! # Structure of pseudo-parabolic subgroups

This module states the smooth connected affine structure target for the actual
source of a pseudo-parabolic inclusion. It does not prove the target.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field, a pseudo-parabolic subgroup of a smooth connected affine
group scheme is itself smooth, connected and affine. -/
def PseudoParabolicSubgroupStructureStatement : Prop :=
  ∀ (k : Type u) [Field k] (G P : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : P ⟶ G), IsPseudoParabolicSubgroup i →
      Smooth P.X.hom ∧ ConnectedSpace P.X.left ∧ IsAffineHom P.X.hom

end Langlands.GroupScheme
