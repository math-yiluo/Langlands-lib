import Langlands.GroupScheme.Reductive.AutomorphismSchemeGeometryFromLocalModels
import Langlands.GroupScheme.Reductive.AffinePinnedAutomorphismSchemeRepresentatives
import Langlands.GroupScheme.Reductive.AffinePinnedIsomorphismTheoremProof
import Langlands.GroupScheme.Reductive.PinnedOuterIsomorphismChartProof
import Langlands.GroupScheme.Adjoint.RelativeExistenceProof

/-! # Full relative reductive automorphism-scheme geometry -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- Every reductive group scheme has a smooth separated full automorphism
scheme, with the exact relative adjoint quotient and outer geometry. -/
theorem reductiveAutomorphismSchemeGeometry :
    ReductiveAutomorphismSchemeGeometryStatement.{u} :=
  reductiveAutomorphismSchemeGeometry_of_pinnedLocalRepresentatives
    pinnedOuterIsomorphismChart relativeAdjointQuotientExistence
    (affinePinnedAutomorphismRepresentatives_of_pinnedClassification
      affinePinnedIsomorphismTheorem)

end Langlands.GroupScheme
