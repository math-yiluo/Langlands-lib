import Langlands.GroupScheme.Absolute.Borel

/-! # Normal unipotent subgroups lie in every Borel subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, a smooth connected unipotent normal closed subgroup of
a smooth connected affine group scheme lies in every Borel subgroup on every test scheme
(Milne 2017, Remark 17.31, for unipotent subgroups). -/
def NormalUnipotentBorelContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ H),
    IsClosedSubgroup i → Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
    (SubgroupFunctor.range i).IsNormal →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ H),
      IsBorelSubgroup c → SubgroupFunctor.range i ≤ SubgroupFunctor.range c

end Langlands.GroupScheme
