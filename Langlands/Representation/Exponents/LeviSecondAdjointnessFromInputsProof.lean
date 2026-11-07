import Langlands.Representation.Exponents.LeviSecondAdjointnessFromInputsStatement
import Langlands.Representation.Exponents.LeviSecondAdjointnessStructure

/-! # Proof of `LeviSecondAdjointnessFromInputsStatement`

The implication is `leviSecondAdjointness_of_structure`.
-/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Renard VI.9.6 (VI.9.6.1) follows from its remaining published inputs. -/
theorem leviSecondAdjointnessFromInputs :
    LeviSecondAdjointnessFromInputsStatement.{u, v} :=
  fun hPD hOpp hstab h2 hUnimod hStandard hCompact =>
    leviSecondAdjointness_of_structure hPD hOpp hstab h2 hUnimod hStandard hCompact

end Langlands.Aubert.General.RepresentedParabolic
