import Langlands.Global.Arithmetic.CMCharacterStatement
import Langlands.Global.Arithmetic.CharacterPrescriptionStatement

/-!
# CM finite prescription from finite-order global prescription

This proposition isolates the conjugate-quotient reduction in Henniart's
Lemma 2. The unconditional finite-order prescription is an explicit premise;
neither that arithmetic existence result nor this implication is proved here.
-/

noncomputable section

universe u

namespace Langlands.Global

/-- Prescribe on a separated finite set and trivially on its conjugates,
then take the quotient by the conjugate character. -/
def CMFiniteCharacterPrescriptionOfFiniteOrderStatement : Prop :=
  FiniteOrderCharacterPrescriptionStatement.{u} →
    CMFiniteCharacterPrescriptionStatement.{u}

end Langlands.Global
