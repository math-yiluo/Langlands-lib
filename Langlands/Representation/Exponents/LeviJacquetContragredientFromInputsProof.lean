import Langlands.Representation.Exponents.LeviJacquetContragredientFromInputsStatement
import Langlands.Representation.Exponents.LeviJacquetContragredientStructure

/-! # Proof of `LeviJacquetContragredientFromInputsStatement`

The implication is `leviJacquetContragredient_of_structure`.
-/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- The second Theorem of Renard VI.9.6 follows from its remaining published inputs. -/
theorem leviJacquetContragredientFromInputs :
    LeviJacquetContragredientFromInputsStatement.{u, v} :=
  fun hPD hOpp hstab h2 => leviJacquetContragredient_of_structure hPD hOpp hstab h2

end Langlands.Aubert.General.RepresentedParabolic
