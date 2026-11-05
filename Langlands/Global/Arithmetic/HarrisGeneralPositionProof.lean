import Langlands.Global.Arithmetic.AuxiliaryCharacterFirstOrderProof
import Langlands.Global.Arithmetic.AuxiliaryGeneralPositionReductionProof

noncomputable section

universe u

namespace Langlands.Global

/-- The first-order auxiliary construction discharges the full local general-position target. -/
theorem harrisGeneralPosition : HarrisGeneralPositionStatement.{u} :=
  auxiliaryGeneralPositionReduction.{u} auxiliaryCharacterFirstOrder.{u,u}

end Langlands.Global
