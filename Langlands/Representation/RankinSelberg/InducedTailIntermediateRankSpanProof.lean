import Langlands.Representation.RankinSelberg.InducedTailIntermediateHostAssemblyProof
import Langlands.Representation.RankinSelberg.InducedTailIntermediateDiagonalExtensionSpanProof
import Langlands.Representation.Whittaker.TwoBlockExtensionProof
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.LowerBlockQuotientDisintegrationProof
import Langlands.Representation.RankinSelberg.InducedTailIntermediateInverseCharacterProof

/-! # Intermediate-test-rank induced tail Laurent-span inclusion -/

namespace Langlands.RankinSelberg

universe uF uV₁ uV₂ uW

/-- The canonical same-character tail span lies in the full zero-row span
when the test rank lies strictly between the tail and full ranks. -/
theorem inducedTailIntermediateRankSpan :
    InducedTailIntermediateRankSpanStatement.{uF, uV₁, uV₂, uW} :=
  inducedTailIntermediateHostAssembly.{uF, uV₁, uV₂, uW}
    inducedTailIntermediateDiagonalExtensionSpan.{uF, max uF uV₁ uV₂, uW}
    Whittaker.twoBlockWhittakerExtension.{uF, uV₁, uV₂}
    normalizedProductWhittakerType.{uF, max uV₁ uV₂}
    lowerBlockQuotientDisintegration.{uF}
    inducedTailIntermediateInverseCharacter.{uF, uW, uV₂}

end Langlands.RankinSelberg
