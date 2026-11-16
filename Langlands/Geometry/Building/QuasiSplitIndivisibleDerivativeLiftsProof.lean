import Langlands.Geometry.Building.QuasiSplitIndivisibleDerivativeLiftsStatement
import Langlands.Geometry.Building.QuasiSplitHenselianUnitaryDepths
import Langlands.Geometry.Building.AlgebraicRankOneCoordinatesExistenceProof

/-! # Indivisible lifts of all derivatives in actual quasi-split apartments -/

universe u

namespace Langlands.Geometry.Building

/-- Every member of the full derivative set of any full-V6 compatible apartment
of an actual quasi-split group has an indivisible affine lift. -/
theorem quasiSplitIndivisibleDerivativeLifts :
    QuasiSplitIndivisibleDerivativeLiftsStatement.{u} :=
  algebraicRankOneIndivisibleLiftsReduction algebraicRankOneCoordinatesExistence

end Langlands.Geometry.Building
