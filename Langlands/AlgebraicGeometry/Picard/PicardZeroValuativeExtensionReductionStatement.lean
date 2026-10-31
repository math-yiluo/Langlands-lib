import Langlands.AlgebraicGeometry.Picard.PicardZeroValuativeExtensionStatement
import Langlands.AlgebraicGeometry.Picard.ValuationRingAmpleExtensionStatement
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldTranslationDifferenceLiftingStatement
import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroStatement
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceStatement

/-! # Valuative extension of Picard-zero classes from four focused propositions -/

universe u

namespace Langlands.AbelianScheme

/-- Translation-difference lifting and ample existence over algebraically closed fields, the
Picard-zero property of the Mumford family, and ample extension from the generic fibre over a
valuation ring together imply the extension of rigidified Picard-zero classes across a
dominating valuation ring. This proposition is a statement target, not a proof. -/
def PicardZeroValuativeExtensionReductionStatement : Prop :=
  AlgClosedFieldTranslationDifferenceLiftingStatement.{u} →
    Langlands.GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u} →
      MumfordBundlePicardZeroStatement.{u} →
        ValuationRingAmpleExtensionStatement.{u} →
          PicardZeroValuativeExtensionStatement.{u}

end Langlands.AbelianScheme
