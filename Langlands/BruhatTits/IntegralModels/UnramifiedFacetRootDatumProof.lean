import Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumReduction
import Langlands.BruhatTits.IntegralModels.IntegralOppositeFactorsProof

/-! # The derivative root datum of a descended unramified facet model -/

universe u

namespace Langlands.BruhatTits.IntegralModels

/-- The actual reductive quotient of every characterized descended facet model
has the root datum specified by the apartment derivative root-coroot graph. -/
theorem unramifiedFacetRootDatum : UnramifiedFacetRootDatumStatement.{u} :=
  unramifiedFacetRootDatum_of_integralOppositeFactors integralOppositeFactors

end Langlands.BruhatTits.IntegralModels
