import Langlands.GroupScheme.Reductive.RelativeCentralQuotientReduction
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeSubgroupProof
import Langlands.GroupScheme.RelativeCentralMultiplicativeTypeQuotient
import Langlands.GroupScheme.Reductive.MultiplicativeTypeNormalCentralProof

/-! # Central quotients of reductive group schemes -/

universe u

namespace Langlands.GroupScheme

/-- For a reductive group scheme over any base, an fppf quotient by a flat central closed
subgroup is reductive. Its centre pulls back to the source centre, and scheme-theoretic
preimage gives the maximal-torus correspondence. -/
theorem relativeCentralQuotient : RelativeCentralQuotientStatement.{u} :=
  relativeCentralQuotient_of_multiplicativeType_inputs
    relativeMultiplicativeTypeClosedSubgroup
    relativeCentralMultiplicativeTypeQuotient
    multiplicativeTypeNormalCentral

end Langlands.GroupScheme
