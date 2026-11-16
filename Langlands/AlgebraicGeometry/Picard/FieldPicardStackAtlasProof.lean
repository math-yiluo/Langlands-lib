import Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasReduction
import Langlands.AlgebraicGeometry.Picard.FiniteTypeVersalChartReduction
import Langlands.AlgebraicGeometry.Picard.FiniteTypeFormalVersalBundleProof
import Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityProof
import Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationReduction
import Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationProof

/-! # Smooth scheme atlases of the Picard stack over a field: proof -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- For a proper scheme over any field, the actual relative line-bundle groupoid
has a smooth surjective scheme atlas locally of finite type over the field.
The finite-type case comes from the published chart reduction applied to formal
versality, algebraization (from etale completion approximation) and openness of
versality; the field case follows by spreading out to a finite-type model. -/
theorem fieldPicardStackAtlas : FieldPicardStackAtlasStatement.{u} :=
  fieldPicardStackAtlas_of_finiteType
    (PicardGroupoid.finiteTypePicardStackAtlas_of_versalInputs finiteTypeFormalVersalBundle
      (versalAlgebraization_of_etaleApproximation
        CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation)
      picardOpennessOfVersality)

end Langlands.AlgebraicGeometry.Picard
