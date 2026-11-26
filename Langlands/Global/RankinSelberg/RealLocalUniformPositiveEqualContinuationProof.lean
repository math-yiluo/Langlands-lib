import Langlands.Global.RankinSelberg.RealLocalPositiveEqualReduction
import Langlands.Global.RankinSelberg.RealUniformCanonicalRange

/-! # The real positive equal-rank continuation and local functional equation

See the paired Markdown file.
-/

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- Meromorphic continuation and the local functional equation of the real equal-rank
Rankin–Selberg integrals at every positive rank index, for functions in the uniform real
Whittaker models of arbitrary real block lists. -/
theorem realLocalUniformPositiveEqualContinuation :
    RealLocalUniformPositiveEqualContinuationStatement :=
  RealJacquet.realLocalUniformPositiveEqualContinuation_of_canonicalPremises
    RealUniformCanonicalRange.realUniformCanonicalRangePremise
    RealUniformCanonicalRange.realCanonicalStandardEvaluationPremise

end Langlands.Global.RankinSelbergGlobal
