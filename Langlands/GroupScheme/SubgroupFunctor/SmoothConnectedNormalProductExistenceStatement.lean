import Langlands.GroupScheme.SubgroupFunctor.FppfProduct
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Smooth connected represented products of normal closed subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Two smooth connected normal closed subgroups of an affine locally finite-type
group over an arbitrary field have a smooth connected represented fppf product.
The geometric construction is an obligation of this proposition target. -/
def SmoothConnectedNormalFppfProductExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom →
    ∀ (H N : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (j : N ⟶ G),
      IsClosedSubgroup i → Smooth H.X.hom → ConnectedSpace H.X.left →
      (SubgroupFunctor.range i).IsNormal →
      IsClosedSubgroup j → Smooth N.X.hom → ConnectedSpace N.X.left →
      (SubgroupFunctor.range j).IsNormal →
      ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
        SubgroupFunctor.IsFppfProduct (SubgroupFunctor.range i)
          (SubgroupFunctor.range j) p ∧
        Smooth P.X.hom ∧ ConnectedSpace P.X.left

end Langlands.GroupScheme
