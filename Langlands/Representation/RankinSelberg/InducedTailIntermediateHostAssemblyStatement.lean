import Langlands.Representation.RankinSelberg.InducedTailIntermediateDiagonalExtensionSpanStatement
import Langlands.Representation.RankinSelberg.InducedTailIntermediateInverseCharacterStatement
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement
import Langlands.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement
import Langlands.Representation.Whittaker.TwoBlockExtensionStatement

/-! # Exact prerequisites for the intermediate-tail span assembly -/

namespace Langlands.RankinSelberg

universe uF uV₁ uV₂ uW

/-- Five separately owned prerequisites imply the unchanged four-universe
intermediate-tail span statement. This interface supplies none of them. -/
def InducedTailIntermediateHostAssemblyStatement : Prop :=
  InducedTailIntermediateDiagonalExtensionSpanStatement.{uF, max uF uV₁ uV₂, uW} →
  Whittaker.TwoBlockWhittakerExtensionStatement.{uF, uV₁, uV₂} →
  NormalizedProductWhittakerTypeStatement.{uF, max uV₁ uV₂} →
  LowerBlockQuotientDisintegrationStatement.{uF} →
  InducedTailIntermediateInverseCharacterStatement.{uF, uW, uV₂} →
  InducedTailIntermediateRankSpanStatement.{uF, uV₁, uV₂, uW}

end Langlands.RankinSelberg
