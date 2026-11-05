import Langlands.GroupScheme.DVRLiftingAlgebraicDescentStatement
import Langlands.GroupScheme.PseudoCompleteAlgebraicBaseChange

/-! # Proof that the DVR lifting property descends along algebraic field extensions -/

universe u

namespace Langlands.GroupScheme

/-- Proof of `DVRLiftingAlgebraicDescentStatement`. -/
theorem dvrLiftingAlgebraicDescentStatement : DVRLiftingAlgebraicDescentStatement.{u} :=
  fun k L _ _ _ _ X h => PseudoComplete.hasDVRLifting_of_baseChange k L X h

end Langlands.GroupScheme
