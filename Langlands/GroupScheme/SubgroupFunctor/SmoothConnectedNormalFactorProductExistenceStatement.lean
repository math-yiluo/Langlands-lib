import Langlands.GroupScheme.SubgroupFunctor.FppfProduct
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Smooth connected represented products with a normal second factor -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected closed subgroup and a smooth connected normal closed
subgroup of an affine locally finite-type group over an arbitrary field have a
smooth connected represented fppf product, in this order. The first factor need
not be normal. The geometric construction is an obligation of this proposition
target. -/
def SmoothConnectedNormalFactorFppfProductExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom →
    ∀ (H N : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (j : N ⟶ G),
      IsClosedSubgroup i → Smooth H.X.hom → ConnectedSpace H.X.left →
      IsClosedSubgroup j → Smooth N.X.hom → ConnectedSpace N.X.left →
      (SubgroupFunctor.range j).IsNormal →
      ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
        SubgroupFunctor.IsFppfProduct (SubgroupFunctor.range i)
          (SubgroupFunctor.range j) p ∧
        Smooth P.X.hom ∧ ConnectedSpace P.X.left

end Langlands.GroupScheme
