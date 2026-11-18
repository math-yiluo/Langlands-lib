import Langlands.GroupScheme.Rational.WeylCharacterFormula
import Langlands.GroupScheme.Rational.FreudenthalMultiplicityProof

/-! # The Weyl character formula for a split reductive group in characteristic zero

The proof combines the combinatorial reduction
`weylCharacterFormulaStatement_of_freudenthal` (module
`Langlands.GroupScheme.Rational.WeylCharacterFormula`) with Freudenthal's multiplicity formula
`freudenthalMultiplicityStatement` (module
`Langlands.GroupScheme.Rational.FreudenthalMultiplicityProof`). -/

universe u

namespace Langlands.GroupScheme

/-- **The Weyl character formula** (Milne, *Algebraic Groups* (2017), Theorem 22.52, in
characteristic zero) for a split pinning of a group scheme over a field of characteristic
zero. -/
theorem weylCharacterFormulaStatement : WeylCharacterFormulaStatement.{u} :=
  weylCharacterFormulaStatement_of_freudenthal freudenthalMultiplicityStatement

end Langlands.GroupScheme
