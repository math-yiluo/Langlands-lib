import Langlands.AlgebraicGeometry.Picard.PicardZeroLineBundleClassificationProof

/-! # Classification of Picard-zero line bundles up to a base twist -/

universe u

namespace Langlands.AbelianScheme

/-- Classification of geometrically Picard-zero line bundles over arbitrary parameter schemes. -/
theorem picardZeroLineBundleClassificationUpToBaseTwist :
    PicardZeroLineBundleClassificationStatement.{u} :=
  picardZeroLineBundleClassification

end Langlands.AbelianScheme
