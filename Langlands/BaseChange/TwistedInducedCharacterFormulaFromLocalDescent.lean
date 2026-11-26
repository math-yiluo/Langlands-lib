import Langlands.BaseChange.TwistedInducedCharacterFormulaReduction
import Langlands.BaseChange.TwistedVanDijk.Proof

/-! # The twisted induced character formula from the local descent

With the twisted van Dijk formula proved (`TwistedVanDijk.twistedVanDijk`), the reduction
`twistedInducedCharacterFormulaReduction` leaves the local descent of the twisted constant term
(`TwistedLocalDescentStatement`) as the only premise of `TwistedInducedCharacterFormulaStatement`.
See the paired Markdown.
-/

namespace Langlands.BaseChange

universe u v uW

/-- The local descent of the twisted constant term implies the twisted induced character
formula of Henniart–Lemaire (2011), II.4.5 (3). -/
def TwistedInducedCharacterFormulaFromLocalDescentStatement : Prop :=
  TwistedLocalDescentStatement.{u, v} → TwistedInducedCharacterFormulaStatement.{u, v, uW}

/-- `TwistedInducedCharacterFormulaStatement` follows from `TwistedLocalDescentStatement`. -/
theorem twistedInducedCharacterFormula_of_localDescent :
    TwistedInducedCharacterFormulaFromLocalDescentStatement.{u, v, uW} :=
  twistedInducedCharacterFormulaReduction TwistedVanDijk.twistedVanDijk

end Langlands.BaseChange
