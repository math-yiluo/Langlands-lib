import Langlands.GroupScheme.Reductive.Basic

/-! # Closed subgroups of unipotent group schemes over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over a field, every closed subgroup of an affine unipotent group scheme of finite type is
unipotent. This is the subgroup clause of Milne 2017, Corollary 14.7. -/
def UnipotentClosedSubgroupStatement : Prop :=
  ∀ (k : Type u) [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (W : GroupScheme (Spec (CommRingCat.of k))) (w : W ⟶ H),
    IsClosedSubgroup w → IsUnipotent H → IsUnipotent W

end Langlands.GroupScheme
