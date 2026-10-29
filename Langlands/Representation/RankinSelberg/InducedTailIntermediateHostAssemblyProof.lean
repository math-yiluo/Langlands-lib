import Langlands.Representation.RankinSelberg.InducedTailIntermediateHostAssemblyStatement
import Langlands.Representation.RankinSelberg.InducedTailIntermediateHostAssembly

/-! # Exact five-prerequisite intermediate-tail assembly -/

namespace Langlands.RankinSelberg

universe uF uV₁ uV₂ uW

/-- Assemble the unchanged intermediate-tail span from its five exact
prerequisites, without discharging any prerequisite. -/
theorem inducedTailIntermediateHostAssembly :
    InducedTailIntermediateHostAssemblyStatement.{uF, uV₁, uV₂, uW} :=
  InducedTailIntermediate.intermediateRankSpan_of_exact_prerequisites

end Langlands.RankinSelberg
