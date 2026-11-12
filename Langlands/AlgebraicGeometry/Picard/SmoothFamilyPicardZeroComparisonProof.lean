import Langlands.AlgebraicGeometry.Picard.SmoothFamilyPicardZeroComparisonReduction
import Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityProof
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldTranslationDifferenceLiftingProof

/-! # Smooth-family algebraic triviality and translation invariance

Supply the four published geometric theorems to the comparison reduction,
including its geometric-fibre, rigidified-family and rigidified-class lifts.
-/

universe u

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The field smooth-family comparison and its three lifts over arbitrary bases. -/
theorem smoothFamilyPicardZeroComparison :
    SmoothFamilyPicardZeroComparisonStatement.{u} :=
  smoothFamilyPicardZeroComparison_of_inputs
    fieldCubeTrivialitySmoothThird smoothGeometricIntegrality
    GroupScheme.algebraicallyClosedFieldAmpleExistence
    algClosedFieldTranslationDifferenceLifting

end Langlands.AbelianScheme
