import Langlands.AlgebraicGeometry.Picard.FieldPicardZeroComponentForward
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyPicardZeroComparisonProof

/-! # Geometric Picard-zero families and the full Picard origin component -/

universe u

namespace Langlands.AbelianScheme

/-- The geometric Picard-zero comparison for every supplied universal field Picard family. -/
theorem fieldPicardZeroGeometricComponentComparison :
    FieldPicardZeroGeometricComponentComparisonStatement.{u} :=
  fieldPicardZeroGeometricComponentComparison_of smoothFamilyPicardZeroComparison

end Langlands.AbelianScheme
