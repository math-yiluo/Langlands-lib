import Langlands.Representation.RankinSelberg.SquareIntegrablePoleOrderCharacterizationReduction
import Langlands.Representation.RankinSelberg.SquareIntegrableDataLFactorProof
import Langlands.Representation.RankinSelberg.TemperedLFactorProof
import Langlands.Representation.RankinSelberg.LanglandsTypeLFactorProof
import Langlands.Representation.RankinSelberg.SquareIntegrableLFactorProof
import Langlands.Representation.RankinSelberg.SegmentHeadLFactorReduction
import Langlands.Representation.RankinSelberg.SupercuspidalEqualRankLFactorProof
import Langlands.Representation.Classification.SquareIntegrableLanglandsExhaustionProof
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationProof
import Langlands.Representation.Classification.SquareIntegrableEqualExponentGroupingProof
import Langlands.Representation.Classification.RegularLanglandsDataUniquenessProof

/-!
# Henniart's separation by pole orders

Henniart 2002, Théorème 1.7(b): a non-supercuspidal irreducible representation
`π` of `GL_N(F)`, `N ≥ 2`, is determined by the orders of the poles at `s = 0`
of `L(s, π × ρ)` for the irreducible essentially square-integrable `ρ` of
`GL_r(F)`, `1 ≤ r ≤ N - 1`.

The published reduction
`squareIntegrablePoleOrderCharacterization_of_classification` derives the
statement from five prerequisites; each is now a proved Library theorem.
-/

noncomputable section

namespace Langlands.RankinSelberg

universe uF uV uW

/-- **Henniart 2002, Théorème 1.7(b).** Let `π` and `π'` be irreducible
admissible representations of `GL_(n+2)(F)`, `π` not supercuspidal. If for
every irreducible essentially square-integrable representation `ρ` of
`GL_(r+1)(F)`, `r ≤ n`, the certified factors `L(s, π × ρ)` and `L(s, π' × ρ)`
have poles of the same order at `s = 0`, then `π ≃ π'`. -/
theorem squareIntegrablePoleOrderCharacterization :
    SquareIntegrablePoleOrderCharacterizationStatement.{uF, uV, uW} :=
  squareIntegrablePoleOrderCharacterization_of_classification
    (fun _ _ F => Classification.squareIntegrableLanglandsExhaustion.{uF, uV} F
      F.canonicalTopologicalData)
    (fun _ _ F => Classification.squareIntegrableLanglandsClassification.{uF, uV} F
      F.canonicalTopologicalData)
    squareIntegrableDataLFactor.{uF, uV, uW}
    (segmentHeadLFactor_of_squareIntegrable squareIntegrableLFactor squareIntegrableLFactor)
    supercuspidalEqualRankLFactor.{uF, max uF uV, max uF uV}

end Langlands.RankinSelberg
