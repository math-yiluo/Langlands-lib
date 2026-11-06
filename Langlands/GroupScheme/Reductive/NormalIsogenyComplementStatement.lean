import Langlands.GroupScheme.Reductive.CommutingMultiplication
import Langlands.GroupScheme.Reductive.Semisimple

/-! # Semisimple normal complements over an arbitrary field -/

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A prescribed smooth connected closed normal subgroup of a semisimple field group
has a semisimple commuting normal complement with central-isogeny multiplication.
This module states the structural proposition and does not prove it. -/
def SemisimpleNormalIsogenyComplementStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple G →
    ∀ (j : H ⟶ G), IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
      (SubgroupFunctor.range j).IsNormal →
      IsSemisimple H ∧
      ∃ (K : GroupScheme (Spec (CommRingCat.of k))) (i : K ⟶ G),
        IsSemisimple K ∧ IsClosedSubgroup i ∧ (SubgroupFunctor.range i).IsNormal ∧
        IsSemisimple (H ⊗ K) ∧
        ∃ hc : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ H.X) (y : T ⟶ K.X),
          Commute (x ≫ j.hom.hom) (y ≫ i.hom.hom),
          IsCentralIsogeny (commutingSubgroupMultiplicationHom j i hc)

end Langlands.GroupScheme
