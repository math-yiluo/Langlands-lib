import Langlands.GroupScheme.Reductive.PinnedOuterIsomorphismChartConstruction
import Langlands.GroupScheme.Reductive.AffinePinnedIsomorphismReduction
import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismTheoremProof
import Langlands.GroupScheme.Reductive.RelativePinnedComparisonProof

/-! # Constant outer-isomorphism charts for pinned split reductive models -/

universe u

namespace Langlands.GroupScheme

/-- The unchanged all-test constant outer-isomorphism chart statement. -/
theorem pinnedOuterIsomorphismChart : PinnedOuterIsomorphismChartStatement.{u} :=
  pinnedOuterIsomorphismChart_of_pinnedTheorems
    (affinePinnedIsomorphismTheorem_of_unpinned affineSplitIsomorphismTheorem)
    AffinePinnedModel.hasFppfLocalPinnedRepresentatives

end Langlands.GroupScheme
