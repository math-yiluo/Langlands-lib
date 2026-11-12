import Langlands.AlgebraicGeometry.Picard.PicardZeroValuativeExtensionStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroValuativeExtensionReduction
import Langlands.AlgebraicGeometry.Picard.ValuationRingAmpleExtensionProof
import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldTranslationDifferenceLiftingProof
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof

/-! # Extension of rigidified Picard-zero classes across a dominating valuation ring

The published reduction is applied to the four published unconditional proofs.
-/

universe u

namespace Langlands.AbelianScheme

/-- Every rigidified Picard-zero class over a valuation domain's fraction field
extends across a dominating valuation domain after a field extension. -/
theorem picardZeroValuativeExtension : PicardZeroValuativeExtensionStatement.{u} :=
  picardZeroValuativeExtension_of_prerequisites
    algClosedFieldTranslationDifferenceLifting.{u}
    Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence.{u}
    mumfordBundlePicardZero.{u}
    valuationRingAmpleExtension.{u}

end Langlands.AbelianScheme
