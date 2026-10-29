import Langlands.Representation.RankinSelberg.InducedTailIntermediateDiagonalExtensionSpanStatement
import Langlands.Representation.RankinSelberg.InducedTailIntermediateQuotientAssembly

/-! # Conditional intermediate-tail span assembly -/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- The retained diagonal extension, Whittaker type and actual measure transfer
give the conditional intermediate-tail span conclusion. -/
theorem inducedTailIntermediateDiagonalExtensionSpan :
    InducedTailIntermediateDiagonalExtensionSpanStatement.{uF, uV, uW} := by
  intro p _ F n d c₀ k hd
  exact InducedTailIntermediate.mem_full_zetaSpan_of_diagonal_extension
    p F n d c₀ k hd

end Langlands.RankinSelberg
