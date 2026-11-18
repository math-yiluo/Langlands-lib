import Langlands.GroupScheme.Reductive.RankOneCentralCoverStatement
import Langlands.GroupScheme.Reductive.RankOneCoverOfRootCell
import Langlands.GroupScheme.Reductive.RankOneFlagCrux

/-! # The rank-one central cover

The proof of `RankOneCentralCoverStatement`: the local line crux gives a root cell, and a root
cell gives the central cover. See the paired Markdown.
-/

universe u

namespace Langlands.GroupScheme

/-- **The rank-one SL₂ central cover.** -/
theorem rankOneCentralCover : RankOneCentralCoverStatement.{u} :=
  RankOneLocalCover.rankOneCentralCover_of_inputs
    (by
      intro k _ G hG T hT i α αv xp xm D h2
      exact rankOneCentralCover_of_rootCell hG hT D h2)
    RankOneLocalCover.localLineCrux

end Langlands.GroupScheme
