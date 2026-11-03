import Langlands.GroupScheme.SubgroupFunctor.FppfProduct
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Represented products with a normal closed subgroup -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A closed subgroup and a normal closed subgroup of an affine locally
finite-type group over an arbitrary field have a represented fppf product.
The geometric construction is an obligation of this proposition target. -/
def NormalFactorFppfProductExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom →
    ∀ (H N : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (j : N ⟶ G),
      IsClosedSubgroup i → IsClosedSubgroup j → (SubgroupFunctor.range j).IsNormal →
      ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
        SubgroupFunctor.IsFppfProduct (SubgroupFunctor.range i)
          (SubgroupFunctor.range j) p

end Langlands.GroupScheme
