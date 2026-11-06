import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleFromSectionLifting
import Langlands.AlgebraicGeometry.Modules.ProperFibrePowerSectionLiftingProof

/-! # Spreading ampleness of a specified line bundle from a proper fibre -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- A specified line bundle that is ample on one fibre of a proper family over a
locally noetherian base is ample over an affine neighbourhood of that base point. -/
theorem properFibreAmpleSpreading : ProperFibreAmpleSpreadingStatement.{u} :=
  properFibreAmpleSpreading_of_powerSectionLifting
    Modules.properFibrePowerSectionLifting

end Langlands.AlgebraicGeometry.Picard
