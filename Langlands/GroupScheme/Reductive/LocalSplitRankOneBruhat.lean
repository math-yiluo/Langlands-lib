import Langlands.GroupScheme.Reductive.LocalSplitRootPairLaws
import Langlands.GroupScheme.Reductive.LocalSplitRankOneBruhatStatement

/-! # The rank-one Bruhat relation over an arbitrary local ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open LocalSplitCell

/-- Weyl-normalized simple root data satisfy the exact unit-denominator
Bruhat relation over every commutative local ring. -/
theorem localSplitRankOneBruhat : LocalSplitRankOneBruhatStatement.{u} := by
  intro R _ _ G _ hG I _ _ i hi hmax J P hP b v hp hn a ha
  have hm : IsRootParametrization i (-P.root a) (v (P.reflectionPerm a a)) := by
    simpa only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
      using (hp a ha).2
  have h := localSplitRootPairLaws R G hG I i hi hmax J P hP a
    (v a) (v (P.reflectionPerm a a)) (hp a ha).1 hm (hn a ha)
  intro B _ s x y d hd
  exact h.2.2.2 (Over.mk s) x y d hd

end Langlands.GroupScheme
