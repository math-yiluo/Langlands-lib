import Langlands.GroupScheme.Adjoint.RelativeExistenceProof
import Langlands.GroupScheme.Reductive.AffinePinnedAutomorphismSchemeRepresentatives
import Langlands.GroupScheme.Reductive.AffinePinnedIsomorphismTheoremProof
import Langlands.GroupScheme.Reductive.AutomorphismSchemeGeometryFromLocalModels
import Langlands.GroupScheme.Reductive.FpqcLocalIsomorphismProof
import Langlands.GroupScheme.Reductive.IsomorphismSchemeFromGeometry

/-! # Full Isom representability for generically isomorphic reductive DVR groups -/

universe u

namespace Langlands.GroupScheme

/-- The full natural Isom functor has a scheme representative over the DVR. -/
theorem genericIsomorphismSchemeExistence :
    GenericIsomorphismSchemeExistenceStatement.{u} := by
  have hPinned := affinePinnedIsomorphismTheorem.{u}
  have hAdj := relativeAdjointQuotientExistence.{u}
  have hChart := pinnedOuterIsomorphismChart_of_pinnedTheorems hPinned
    AffinePinnedModel.hasFppfLocalPinnedRepresentatives
  have hLocal := affinePinnedAutomorphismRepresentatives_of_pinnedClassification hPinned
  exact genericIsomorphismSchemeExistence_of_geometry
    (reductiveAutomorphismSchemeGeometry_of_pinnedLocalRepresentatives hChart hAdj hLocal)
    hAdj reductiveFpqcLocalIsomorphism

end Langlands.GroupScheme
