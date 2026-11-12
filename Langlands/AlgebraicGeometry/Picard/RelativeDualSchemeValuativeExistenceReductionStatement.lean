import Langlands.AlgebraicGeometry.Picard.PicardZeroValuativeExtensionStatement
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeValuativeExistenceStatement

/-! # Reduction of dual valuative existence to extension of Picard-zero classes -/

universe u

namespace Langlands.AbelianScheme

/-- Extension of rigidified Picard-zero classes across a dominating valuation ring
implies valuative existence over the original valuation ring for the chosen dual. -/
def RelativeDualSchemeValuativeExistenceReductionStatement : Prop :=
  PicardZeroValuativeExtensionStatement.{u} →
    RelativeDualSchemeValuativeExistenceStatement.{u}

end Langlands.AbelianScheme
