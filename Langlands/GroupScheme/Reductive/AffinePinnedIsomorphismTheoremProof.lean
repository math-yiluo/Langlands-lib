import Langlands.GroupScheme.Reductive.AffinePinnedIsomorphismReduction
import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismTheoremProof

/-! # The pinned Isomorphism Theorem over an affine base -/

universe u

namespace Langlands.GroupScheme

/-- The unchanged affine pinned Isomorphism Theorem, in every universe. -/
theorem affinePinnedIsomorphismTheorem : AffinePinnedIsomorphismTheoremStatement.{u} :=
  affinePinnedIsomorphismTheorem_of_unpinned affineSplitIsomorphismTheorem

end Langlands.GroupScheme
