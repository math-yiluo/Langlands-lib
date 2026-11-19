import Langlands.GroupScheme.Reductive.RankOneCentralCoverProof
import Langlands.GroupScheme.Reductive.IndependentRootCellReduction

/-! # Rank-one actual root support and root-space lines over algebraically closed fields -/

universe u

namespace Langlands.GroupScheme

/-- Every actual root is one of the signed pair, and both actual root spaces are lines. -/
theorem algClosedRankOneRootSupportLines : AlgClosedRankOneRootSupportLinesStatement.{u} :=
  algClosedRankOneRootSupportLines_of_centralCover rankOneCentralCover

end Langlands.GroupScheme
