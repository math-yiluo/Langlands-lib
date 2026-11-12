import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationReduction
import Langlands.Representation.RankinSelberg.SupercuspidalUnequalRankLFactorReduction
import Langlands.Representation.RankinSelberg.LanglandsTypeLFactorProof
import Langlands.Representation.RankinSelberg.TemperedSupercuspidalPoleReduction
import Langlands.Representation.RankinSelberg.SquareIntegrableLFactorProof
import Langlands.Representation.RankinSelberg.TemperedLFactorProof
import Langlands.Representation.Classification.TemperedBlockExhaustionProof
import Langlands.Representation.Classification.SupercuspidalTemperedQuotientSingleBlockProof

/-!
# Henniart 2002, Théorème 1.6(b)

The characterization of supercuspidal representations of `GL_(n+2)(F)` by
L-factors of pairs with supercuspidal representations of smaller rank, from the
conditional reduction and the published proofs of its five inputs.
-/

noncomputable section

namespace Langlands.RankinSelberg

universe uF uV uW

/-- The pole statement for twisted tempered blocks, from tempered block
exhaustion and JPSS (8.2) and (8.4). -/
theorem temperedTwistSupercuspidalPole :
    TemperedTwistSupercuspidalPoleStatement.{uF, uV, uW} :=
  temperedTwistSupercuspidalPoleReduction
    (fun _ _ F => Classification.temperedBlockExhaustion F F.canonicalTopologicalData)
    squareIntegrableLFactor temperedLFactor

/-- Henniart 2002, Théorème 1.6(b), (i) ⇔ (ii), printed pages 590-591: an
irreducible admissible representation `π` of `GL_(n+2)(F)` is supercuspidal if
and only if `L(s, π × ρ) = 1` for every irreducible supercuspidal
representation `ρ` of `GL_(r+1)(F)`, `r ≤ n`. -/
theorem supercuspidalLFactorCharacterization :
    SupercuspidalLFactorCharacterizationStatement.{uF, uV, uW} :=
  SupercuspidalLFactorCharacterization.supercuspidalLFactorCharacterization_of
    supercuspidalUnequalRankLFactor langlandsTypeLFactor
    Classification.supercuspidalTemperedQuotientSingleBlock
    Classification.supercuspidalTemperedQuotientSingleBlock
    temperedTwistSupercuspidalPole

end Langlands.RankinSelberg
