import Langlands.GroupScheme.Reductive.RootLieLineFromCentralCover
import Langlands.GroupScheme.Reductive.RankOneCentralCoverProof

/-! # Split root Lie lines via the rank-one central cover -/

universe u

namespace Langlands.GroupScheme

/-- Every root Lie space of a split maximal torus in a connected reductive
group over a field is a line. -/
theorem splitRootLieLine_independent : SplitRootLieLineStatement.{u} :=
  splitRootLieLine_of_centralCover rankOneCentralCover

end Langlands.GroupScheme
