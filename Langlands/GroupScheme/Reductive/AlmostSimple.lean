import Langlands.GroupScheme.Reductive.Semisimple

/-! # Almost-simple field group schemes -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An almost-simple group is semisimple and noncommutative, and its only
smooth connected closed normal subgroups are the identity and the whole group.
This uses the corrected definition of Milne, Algebraic Groups, 19.7. -/
structure IsAlmostSimple {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) : Prop where
  isSemisimple : IsSemisimple G
  noncommutative : ¬ ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X), Commute x y
  normalSubgroup_trivial_or_full :
    ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      IsClosedSubgroup i → Smooth H.X.hom → ConnectedSpace H.X.left →
      (SubgroupFunctor.range i).IsNormal →
      SubgroupFunctor.range i = ⊥ ∨ SubgroupFunctor.range i = ⊤

end Langlands.GroupScheme
