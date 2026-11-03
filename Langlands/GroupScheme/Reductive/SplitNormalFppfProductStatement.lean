import Langlands.GroupScheme.SubgroupFunctor.FppfProduct
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Split unipotence of represented products of split normal closed subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected represented fppf product of two split smooth connected normal
closed subgroups of an affine locally finite-type group over an arbitrary field is
split unipotent. -/
def SplitNormalFppfProductStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom →
    ∀ (H N : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (j : N ⟶ G),
      IsClosedSubgroup i → Smooth H.X.hom → ConnectedSpace H.X.left →
      (SubgroupFunctor.range i).IsNormal → RelativeRoot.IsSplitUnipotent H →
      IsClosedSubgroup j → Smooth N.X.hom → ConnectedSpace N.X.left →
      (SubgroupFunctor.range j).IsNormal → RelativeRoot.IsSplitUnipotent N →
      ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
        SubgroupFunctor.IsFppfProduct (SubgroupFunctor.range i)
          (SubgroupFunctor.range j) p →
        Smooth P.X.hom → ConnectedSpace P.X.left →
        RelativeRoot.IsSplitUnipotent P

end Langlands.GroupScheme
