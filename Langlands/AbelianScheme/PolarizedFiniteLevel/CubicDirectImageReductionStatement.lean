import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicDirectImageStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyStatement

/-! # Reduction of the cubic direct-image theorem to algebraically closed fibres -/

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- The cohomology of the actual cubic diagonal bundle over algebraically closed fields
implies the prescribed rank and canonical arbitrary base change of its direct image.
This is a theorem target. -/
def CubicDirectImageReductionStatement : Prop :=
  CubicFibreCohomologyStatement.{u} → CubicDirectImageStatement.{u}

end Langlands.AbelianScheme.PolarizedFiniteLevel
