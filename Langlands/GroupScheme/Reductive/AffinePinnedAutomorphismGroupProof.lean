import Langlands.GroupScheme.Reductive.AffinePinnedAutomorphismSplittingGeometry
import Langlands.GroupScheme.Reductive.AffinePinnedIsomorphismReduction
import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismTheoremProof
import Langlands.GroupScheme.Reductive.RelativePinnedComparisonProof

/-! # Automorphisms of a pinned split reductive group over a connected affine base -/

universe u

namespace Langlands.GroupScheme

/-- The unchanged affine pinned automorphism-group statement, in every universe. -/
theorem affinePinnedAutomorphismGroup :
    AffinePinnedAutomorphismGroupStatement.{u} :=
  affinePinnedAutomorphismGroup_of_localPinnedRepresentatives
    (affinePinnedIsomorphismTheorem_of_unpinned affineSplitIsomorphismTheorem)
    AffinePinnedModel.hasFppfLocalPinnedRepresentatives

end Langlands.GroupScheme
