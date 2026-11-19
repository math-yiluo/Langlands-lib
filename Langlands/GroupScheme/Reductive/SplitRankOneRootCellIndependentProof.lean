import Langlands.GroupScheme.Reductive.IndependentRootCellReduction
import Langlands.GroupScheme.Reductive.RankOneCentralCoverProof

/-! # The independent proof of the split rank-one root cell -/

universe u

namespace Langlands.GroupScheme

/-- The split rank-one root cell over an arbitrary field, via the independent central cover. -/
theorem splitRankOneRootCellIndependent : SplitRankOneRootCellStatement.{u} :=
  splitRankOneRootCell_of_centralCover (rankOneCentralCover.{u})

end Langlands.GroupScheme
