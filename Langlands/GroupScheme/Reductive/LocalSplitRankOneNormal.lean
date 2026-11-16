import Langlands.GroupScheme.Reductive.LocalSplitRootPairLaws
import Langlands.GroupScheme.Reductive.LocalSplitRankOneNormalStatement

/-! # Rank-one normalization over an arbitrary local ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open LocalSplitCell

/-- Weyl-normalized simple root data satisfy both root conjugations and
the exact coroot square over every commutative local ring. -/
theorem localSplitRankOneNormal : LocalSplitRankOneNormalStatement.{u} := by
  intro R _ _ G _ hG I _ _ i hi hmax J P hP b v hp hn a ha
  have hm : IsRootParametrization i (-P.root a) (v (P.reflectionPerm a a)) := by
    simpa only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
      using (hp a ha).2
  have h := localSplitRootPairLaws R G hG I i hi hmax J P hP a
    (v a) (v (P.reflectionPerm a a)) (hp a ha).1 hm (hn a ha)
  refine ⟨?_, ?_, ?_⟩
  · intro B _ s x
    exact h.1 (Over.mk s) x
  · intro B _ s x
    exact h.2.1 (Over.mk s) x
  · have hs := h.2.2.1 (𝟙_ (Over (Spec (CommRingCat.of R))))
    change ((𝟙 _ ≫ weylPoint (v a) (v (P.reflectionPerm a a))) *
      (𝟙 _ ≫ weylPoint (v a) (v (P.reflectionPerm a a)))) = _ at hs
    simpa only [Category.id_comp] using hs

end Langlands.GroupScheme
