import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Commuting normal complements in semisimple groups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A smooth connected closed normal subgroup of a semisimple group over an
algebraically closed field has a closed normal complement commuting with it on
every test scheme, such that the multiplication morphism from the product is
flat and surjective. This is a structural proposition target. -/
def SemisimpleNormalComplementStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G H : GroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple G →
    ∀ (j : H ⟶ G), IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
      (SubgroupFunctor.range j).IsNormal →
      ∃ (K : GroupScheme (Spec (CommRingCat.of k))) (i : K ⟶ G),
        IsClosedSubgroup i ∧ (SubgroupFunctor.range i).IsNormal ∧
        (∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ H.X) (y : T ⟶ K.X),
          Commute (x ≫ j.hom.hom) (y ≫ i.hom.hom)) ∧
        Flat (subgroupMultiplication j i).left ∧
        Surjective (subgroupMultiplication j i).left

end Langlands.GroupScheme
