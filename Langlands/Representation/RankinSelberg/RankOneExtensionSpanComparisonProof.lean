import Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonAssembly
import Langlands.Representation.RankinSelberg.RankOneExtensionLowerJacquetFunctionalProof
import Langlands.Representation.RankinSelberg.LowerBlockQuotientDisintegrationProof

/-!
# Proof of the rank-one extension span comparison

The closed theorem `rankOneExtensionSpanComparison`, obtained from the conditional assembly
`rankOneExtensionSpanComparison_of_statements` and the published proofs of its two
hypotheses.
-/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- JPSS (1983) Lemma 5.5 for `t + 3 ≤ r + 1`: the Laurent span of the block-one base
integrals is contained in the Laurent span of the block-zero integrals of the lower
induction. -/
theorem rankOneExtensionSpanComparison :
    RankOneExtensionSpanComparisonStatement.{uF, uV, uW} :=
  rankOneExtensionSpanComparison_of_statements lowerBlockQuotientDisintegration
    rankOneExtensionLowerJacquetFunctional

end Langlands.RankinSelberg
