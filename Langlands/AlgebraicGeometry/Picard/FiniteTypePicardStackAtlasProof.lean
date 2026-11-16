import Langlands.AlgebraicGeometry.Picard.FiniteTypePicardStackAtlasStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypeVersalChartReduction
import Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationReduction
import Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityProof
import Langlands.AlgebraicGeometry.Picard.FiniteTypeFormalVersalBundleProof
import Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationProof

/-! # Smooth scheme atlases of the Picard stack over a finite-type `ℤ`-algebra: proof -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- For every commutative ring `R` of finite type over `ℤ` and every proper flat scheme
`X` over `Spec R`, the actual relative line-bundle groupoid has a smooth surjective scheme
atlas locally of finite type over `Spec R`. Formal versality, algebraization (from etale
approximation) and openness of versality are the three inputs of the published chart
reduction. -/
theorem finiteTypePicardStackAtlas : FiniteTypePicardStackAtlasStatement.{u} :=
  PicardGroupoid.finiteTypePicardStackAtlas_of_versalInputs finiteTypeFormalVersalBundle
    (versalAlgebraization_of_etaleApproximation
      CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation)
    picardOpennessOfVersality

end Langlands.AlgebraicGeometry.Picard
