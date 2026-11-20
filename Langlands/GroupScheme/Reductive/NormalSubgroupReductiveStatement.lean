import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth connected normal subgroups of reductive groups are reductive (Milne 21.53) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 21.53: over every field `k`, a smooth connected closed normal
subgroup `n : N ⟶ G` of a connected reductive group `G` is connected reductive. -/
def NormalSubgroupReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G),
      IsClosedSubgroup n → Smooth N.X.hom → ConnectedSpace N.X.left →
        (SubgroupFunctor.range n).IsNormal → IsConnectedReductive N

end Langlands.GroupScheme
