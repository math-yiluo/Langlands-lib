import Langlands.Representation.RankinSelberg.InducedTailEqualRankSpanProof
import Langlands.Representation.RankinSelberg.InducedTailSmallerRankSpanProof
import Langlands.Representation.RankinSelberg.InducedTailIntermediateRankSpanProof

/-! # The three direct-rank induced tail Laurent-span inclusions -/

namespace Langlands.RankinSelberg

universe uF uV₁ uV₂ uW

/-- Assemble the three closed direct-rank span comparisons. -/
theorem inducedTailSpan :
    InducedTailSpanStatement.{uF, uV₁, uV₂, uW} :=
  ⟨inducedTailEqualRankSpan.{uF, uV₁, uV₂, uW},
    inducedTailSmallerRankSpan.{uF, uV₁, uV₂, uW},
    inducedTailIntermediateRankSpan.{uF, uV₁, uV₂, uW}⟩

end Langlands.RankinSelberg
