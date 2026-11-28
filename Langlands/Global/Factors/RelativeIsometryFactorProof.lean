import Langlands.Global.Factors.RelativeIsometryFactorRealReduction
import Langlands.Global.RankinSelberg.RealLocalUniformUnequalContinuationProof
import Langlands.Global.RankinSelberg.RealUnequalOrdinaryPlaceTestsProof
import Langlands.Global.RankinSelberg.RealEqualLastRowPlaceTestsProof

/-! # Determinants and pair factors of the relative generated isometry -/

set_option autoImplicit false

universe uF uW uP uE

namespace Langlands.Global.PoleComparison

open RankinSelbergGlobal

/-- Determinant, pair L-factor and pair epsilon-factor compatibility for every
relative generated positive isometry under the certified pole comparisons. -/
theorem relativeIsometryFactor : RelativeIsometryFactorStatement.{uF, uW, uP, uE} :=
  relativeIsometryFactorStatement_of_realContinuation_and_tests
    realLocalUniformUnequalContinuation
    (fun F _ _ _ ψ hψ r t h _ => realUnequalOrdinaryPlaceTests F ψ hψ r t h)
    realEqualOrdinaryPlaceTests

end Langlands.Global.PoleComparison
