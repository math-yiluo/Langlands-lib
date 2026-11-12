import Langlands.Representation.RankinSelberg.SquareIntegrableDataLFactorReduction
import Langlands.Representation.RankinSelberg.TemperedLFactorProof
import Langlands.Representation.RankinSelberg.LanglandsTypeLFactorProof
import Langlands.Representation.Classification.SquareIntegrableEqualExponentGroupingProof
import Langlands.Representation.Classification.RegularLanglandsDataUniquenessProof

/-!
# L-factors of pairs through essentially square-integrable Langlands data

JPSS 1983, Theorem (9.5), in the product form of Henniart 2002, 2.8. The
published reduction is closed by the proved equal-exponent grouping, JPSS
Propositions (8.4) and (9.4)(3), and ordered tempered Langlands-data
uniqueness.
-/

noncomputable section

namespace Langlands.RankinSelberg

universe uF uV uW

/-- JPSS 1983, Theorem (9.5): `L(s, π × σ)` is the double product of the
L-factors of the pairs of essentially square-integrable blocks. -/
theorem squareIntegrableDataLFactor :
    SquareIntegrableDataLFactorStatement.{uF, uV, uW} :=
  squareIntegrableDataLFactor_of_prerequisites
    (fun _ _ F => Classification.squareIntegrableEqualExponentGrouping.{uF, uV}
      F F.canonicalTopologicalData)
    (fun _ _ F => Classification.squareIntegrableEqualExponentGrouping.{uF, uW}
      F F.canonicalTopologicalData)
    temperedLFactor.{uF, max uF uV, max uF uW}
    langlandsTypeLFactor.{uF, max uF uV, max uF uW}
    glRegularLanglandsDataUniqueness.{uF, uV}
    glRegularLanglandsDataUniqueness.{uF, uW}

end Langlands.RankinSelberg
