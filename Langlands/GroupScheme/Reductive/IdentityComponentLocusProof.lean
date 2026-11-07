import Langlands.GroupScheme.Reductive.IdentityComponentLocusLiftingReduction
import Langlands.GroupScheme.Torus.RelativeLiftingProof

/-! # Openness of the reductive geometric identity-component locus -/

universe u

namespace Langlands.GroupScheme

/-- The reductive geometric identity-component locus of every smooth affine
group scheme over an arbitrary base is open. -/
theorem identityComponentReductiveLocusOpen :
    IdentityComponentReductiveLocusOpenStatement.{u} :=
  identityComponentReductiveLocusOpen_of_lifting relativeSplitTorusLifting

end Langlands.GroupScheme
