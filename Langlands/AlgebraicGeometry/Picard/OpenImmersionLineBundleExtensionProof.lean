import Langlands.AlgebraicGeometry.Picard.OpenImmersionLineBundleLocalToGlobal
import Langlands.AlgebraicGeometry.Picard.AffineOpenImmersionLineBundleExtensionFromIdeals
import Langlands.AlgebraicGeometry.Picard.QuasiAffineLineBundleIdealEmbeddingProof
import Langlands.AlgebraicGeometry.Picard.OpenImmersionInvertibleIdealExtensionProof

/-! # Extension of line bundles across arbitrary open immersions -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- An actual line bundle extends when the complementary stalks are factorial. -/
theorem openImmersionLineBundleExtension :
    OpenImmersionLineBundleExtensionStatement.{u} :=
  OpenImmersionLineBundleLocalToGlobal.of_affine
    (affineOpenImmersionLineBundleExtension_of_ideals
      quasiAffineLineBundleIdealEmbedding openImmersionInvertibleIdealExtension)

end Langlands.AlgebraicGeometry.Picard
