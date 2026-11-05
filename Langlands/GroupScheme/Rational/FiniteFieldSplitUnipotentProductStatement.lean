import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.SubgroupIntersection

/-! # Statement: rationally surjective products of split unipotent subgroups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- Over a finite field, a product of smooth connected split unipotent
subgroups that covers all rational points is a smooth surjective morphism,
provided its actual intersection is smooth, connected and split. -/
def FiniteFieldSplitUnipotentProductStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k]
    (U V C : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left]
    [Smooth V.X.hom] [IsAffineHom V.X.hom] [ConnectedSpace V.X.left]
    [Smooth C.X.hom] [IsAffineHom C.X.hom] [ConnectedSpace C.X.left]
    (j : V ⟶ U) (c : C ⟶ U),
      IsClosedSubgroup j → IsClosedSubgroup c →
      IsSplitUnipotent U → IsSplitUnipotent V → IsSplitUnipotent C →
      Smooth (subgroupIntersection j c).X.hom →
      ConnectedSpace (subgroupIntersection j c).X.left →
      IsSplitUnipotent (subgroupIntersection j c) →
      (∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X,
        ∃ v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X,
        ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X,
          (v ≫ j.hom.hom) * (z ≫ c.hom.hom) = x) →
      Smooth (subgroupMultiplication j c).left ∧
        Surjective (subgroupMultiplication j c).left

end Langlands.GroupScheme.RelativeRoot
