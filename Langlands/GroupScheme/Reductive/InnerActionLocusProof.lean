import Langlands.GroupScheme.Adjoint.RelativeExistenceProof
import Langlands.GroupScheme.Reductive.AutomorphismSchemeGeometryProof
import Langlands.GroupScheme.Reductive.AutomorphismSchemeReduction

/-! # The clopen inner-action locus for reductive group schemes -/

universe u

namespace Langlands.GroupScheme

/-- The inner part of an arbitrary action on a reductive group scheme is open
and closed and universal for restrictions through the full-centre quotient. -/
theorem reductiveInnerActionLocus : ReductiveInnerActionLocusStatement.{u} :=
  reductiveInnerActionLocus_of_geometry
    reductiveAutomorphismSchemeGeometry relativeAdjointQuotientExistence

end Langlands.GroupScheme
