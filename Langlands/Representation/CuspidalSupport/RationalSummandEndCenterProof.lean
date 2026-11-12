import Langlands.Representation.CuspidalSupport.NormalHeckeHomDetection
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof

/-! Renard VI.4.4, Theorem: proof of `RationalSummandEndCenterStatement`, from the finite-length clause of the
published VI.3.2(ii) proof through `NormalHeckeHomDetection`, without VI.4.1. -/

namespace Langlands.CuspidalSupport

universe uF uV

/-- **Renard VI.4.4, Theorem.** -/
theorem rationalSummandEndCenter : RationalSummandEndCenterStatement.{uF, uV} :=
  rationalSummandEndCenter_of_finiteRestriction rationalNormKernelFiniteRestriction

end Langlands.CuspidalSupport
