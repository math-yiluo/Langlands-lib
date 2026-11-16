import Langlands.GroupScheme.Reductive.IdentityComponentSemisimpleAffineOpen
import Langlands.GroupScheme.Reductive.IdentityComponentSemisimpleLocusLiftingReduction
import Langlands.GroupScheme.Torus.RelativeLiftingProof

/-! # Openness of the semisimple geometric identity-component locus -/

universe u

namespace Langlands.GroupScheme

/-- The semisimple geometric identity-component locus of every smooth affine
 group scheme over an arbitrary base is open. -/
theorem identityComponentSemisimpleLocusOpen :
    IdentityComponentSemisimpleLocusOpenStatement.{u} :=
  identityComponentSemisimpleLocusOpen_of_lifting
    (by
      intro r _ I _ _ G _ _ i hi s hs hself
      exact splitTorus.exists_open_subset_identityComponentSemisimpleLocus
        I G i hi s hs hself)
    relativeSplitTorusLifting

end Langlands.GroupScheme
