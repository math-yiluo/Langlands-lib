import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeValuativeExistenceReduction
import Langlands.AlgebraicGeometry.Picard.PicardZeroValuativeExtensionProof

/-! # Valuative existence for the chosen dual parameter scheme -/

universe u

namespace Langlands.AbelianScheme

/-- The chosen dual has valuative existence over each original valuation ring. -/
theorem relativeDualSchemeValuativeExistence :
    RelativeDualSchemeValuativeExistenceStatement.{u} :=
  relativeDualSchemeValuativeExistenceReduction.{u}
    picardZeroValuativeExtension.{u}

end Langlands.AbelianScheme
