import Langlands.Representation.RankinSelberg.LanglandsPairEpsilonBlockExistence
import Langlands.Representation.Classification.SquareIntegrableLanglandsExhaustionProof
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationProof

/-!
# Existence of epsilon factors of arbitrary irreducible pairs

The proved square-integrable exhaustion and classification, at both carrier
universes, discharge the remaining hypotheses of the block-factor reduction.
-/

namespace Langlands.RankinSelberg

open Classification

universe uF uV uW

/-- Henniart 2002, 2.8: every pair of irreducible admissible representations
of positive-rank p-adic general linear groups has an actual epsilon factor,
for every nontrivial unitary additive character and every supplied self-dual
Haar measure. -/
theorem langlandsPairEpsilonFactorExistence :
    LanglandsPairEpsilonFactorExistenceStatement.{uF, uV, uW} :=
  langlandsPairEpsilonFactorExistence_of_exhaustion_classification.{uF, uV, uW}
    (fun _ _ F =>
      ⟨squareIntegrableLanglandsExhaustion.{uF, uV} F F.canonicalTopologicalData,
        squareIntegrableLanglandsExhaustion.{uF, uW} F F.canonicalTopologicalData⟩)
    (fun _ _ F =>
      ⟨squareIntegrableLanglandsClassification.{uF, uV} F F.canonicalTopologicalData,
        squareIntegrableLanglandsClassification.{uF, uW} F F.canonicalTopologicalData⟩)

end Langlands.RankinSelberg
