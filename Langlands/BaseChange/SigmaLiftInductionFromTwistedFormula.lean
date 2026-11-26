import Langlands.BaseChange.SharedInducedCharacterExpansionFromFormulas
import Langlands.BaseChange.InducedCharacterFormulaFromTwisted

/-! # σ-lift induction from the σ-lift/Shintani equivalence and the twisted character formula

`SigmaLiftInductionStatement` follows from `SigmaLiftCharacterIdentityStatement` at two
universe levels and `TwistedInducedCharacterFormulaStatement` at two universe levels, the
degree-one instance of the latter giving the ordinary formula. These four inputs are explicit
premises, not theorems of this module. See the paired Markdown.
-/

namespace Langlands.BaseChange

/-- The σ-lift/Shintani equivalence for the factors and for the induced representations, and
the twisted induced character formula for the carriers of the factors over `F` (in degree
one) and over `E`, imply the Library's σ-lift induction statement. -/
def SigmaLiftInductionTwistedFormulaReductionStatement.{u, v, uV, uW} : Prop :=
  SigmaLiftCharacterIdentityStatement.{u, v, uV, uW} →
  SigmaLiftCharacterIdentityStatement.{u, v, max u uV, max v uW} →
  TwistedInducedCharacterFormulaStatement.{u, u, uV} →
  TwistedInducedCharacterFormulaStatement.{u, v, uW} →
  SigmaLiftInductionStatement.{u, v, uV, uW}

/-- Compose `inducedCharacterFormula_of_twisted`, `sharedInducedCharacterExpansion_of_formulas`
and `sigmaLiftInductionReduction`. -/
theorem sigmaLiftInduction_of_twistedFormula.{u, v, uV, uW} :
    SigmaLiftInductionTwistedFormulaReductionStatement.{u, v, uV, uW} :=
  fun hBlock hInduced hOrdinary hTwisted =>
    sigmaLiftInductionReduction hBlock hInduced
      (sharedInducedCharacterExpansion_of_formulas
        (inducedCharacterFormula_of_twisted hOrdinary) hTwisted)

end Langlands.BaseChange
