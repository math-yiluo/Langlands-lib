import Langlands.Global.Arithmetic.AuxiliaryCharacterStatement
import Langlands.Global.Arithmetic.GeneralPositionStatement

noncomputable section

universe u

namespace Langlands.Global

/-- The existing exact unit-norm auxiliary-character existence input supplies
the full Harris general-position statement in the actual common closure. -/
def AuxiliaryGeneralPositionReductionStatement : Prop :=
  AuxiliaryCharacterStatement.{u, u} → HarrisGeneralPositionStatement.{u}

end Langlands.Global
