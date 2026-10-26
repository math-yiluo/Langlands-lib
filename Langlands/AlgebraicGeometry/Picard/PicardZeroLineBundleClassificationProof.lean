import Langlands.AlgebraicGeometry.Picard.PicardZeroLineBundleClassificationFromInverse
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation

/-! # Classification of geometrically Picard-zero line bundles up to a base twist -/

universe u

namespace Langlands.AbelianScheme

/-- Every geometrically Picard-zero line bundle on `T ×_S A` is a pullback of the chosen
Poincaré family tensored with a line bundle from `T`. -/
theorem picardZeroLineBundleClassification : PicardZeroLineBundleClassificationStatement.{u} :=
  picardZeroLineBundleClassification_of_inverse
    Langlands.AlgebraicGeometry.Picard.LineBundle.exists_tensorObj_iso_structureSheaf

end Langlands.AbelianScheme
