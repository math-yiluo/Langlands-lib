import Langlands.BaseChange.PseudoCoefficientExistenceReduction
import Langlands.BaseChange.SquareIntegrableNotInduced

/-! # Untwisted pseudo-coefficients from twisted existence alone -/

namespace Langlands.BaseChange

universe u uV

/-- The twisted existence statement, used at `E = F`, `σ = 1`, `l = 1`, implies the
untwisted existence statement. The separate non-induction premise has been proved. -/
def PseudoCoefficientExistenceOfTwistedStatement.{v, w} : Prop :=
  TwistedPseudoCoefficientExistenceStatement.{v, v, w} → PseudoCoefficientExistenceStatement.{v, w}

/-- Discharge the non-induction premise of `pseudoCoefficientExistenceReduction`. -/
theorem pseudoCoefficientExistenceOfTwisted : PseudoCoefficientExistenceOfTwistedStatement.{u, uV} :=
  fun ht => pseudoCoefficientExistenceReduction ht squareIntegrableNotInduced

end Langlands.BaseChange
