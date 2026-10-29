import Langlands.AlgebraicGeometry.Picard.SmoothFamilyPicardZeroComparisonLifts
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyOfTranslationInvariance
import Langlands.AlgebraicGeometry.Picard.TranslationInvarianceOfSmoothFamily

/-! # The smooth-family comparison from its four geometric inputs -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The field comparison, given the theorem of the cube with a smooth third factor,
geometric integrality, ample existence and Proposition (7.21). -/
theorem smoothFamilyTranslationInvariance_of_inputs
    (cube : FieldCubeTrivialitySmoothThirdStatement.{u})
    (integrality : SmoothGeometricIntegrality.{u})
    (ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (lifting : AlgClosedFieldTranslationDifferenceLiftingStatement.{u}) :
    SmoothFamilyTranslationInvarianceStatement.{u} :=
  fun _ _ _ A L ↦
    ⟨isTranslationInvariant_of_isAlgebraicallyTrivialViaSmoothFamily cube A L,
      isAlgebraicallyTrivialViaSmoothFamily_of_isTranslationInvariant integrality ample
        lifting A L⟩

/-- The full aggregate comparison from the same four inputs. -/
theorem smoothFamilyPicardZeroComparison_of_inputs
    (cube : FieldCubeTrivialitySmoothThirdStatement.{u})
    (integrality : SmoothGeometricIntegrality.{u})
    (ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u})
    (lifting : AlgClosedFieldTranslationDifferenceLiftingStatement.{u}) :
    SmoothFamilyPicardZeroComparisonStatement.{u} :=
  smoothFamilyPicardZeroComparison_of_field
    (smoothFamilyTranslationInvariance_of_inputs cube integrality ample lifting)

end Langlands.AbelianScheme
