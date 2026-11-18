import Langlands.GroupScheme.Reductive.RelativeQuasiSplitInnerFormConstruction
import Langlands.GroupScheme.Reductive.RelativePinnedComparisonProof

/-! # Quasi-split inner forms of reductive group schemes over any base -/

universe u

namespace Langlands.GroupScheme

/-- Every reductive group scheme has a quasi-split inner form with a Borel
subgroup containing a closed fibrewise maximal relative torus. -/
theorem relativeQuasiSplitInnerFormExistence :
    RelativeQuasiSplitInnerFormExistenceStatement.{u} :=
  relativeQuasiSplitInnerFormExistence_of_pinnedComparison
    relativePinnedComparisonExistence

end Langlands.GroupScheme
