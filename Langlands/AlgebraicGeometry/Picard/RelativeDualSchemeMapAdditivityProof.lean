import Langlands.AlgebraicGeometry.Picard.DualSchemeMapAdditivity
import Langlands.AlgebraicGeometry.Picard.PicardZeroLineBundleClassificationProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeMapAdditivityStatement
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-! # Additivity of actual dual maps over a quasi-separated base -/

universe u

namespace Langlands.AbelianScheme

/-- For homomorphisms `f g : A ⟶ B` of abelian schemes over a quasi-separated base, the actual
dual map of `f + g` is the sum of the actual dual maps. The quasi-separatedness of the base is
not used. -/
theorem relativeDualSchemeMapAdditivity : RelativeDualSchemeMapAdditivityStatement.{u} := by
  intro preservation stability S _ A B hA hB f g
  exact dualSchemeMap_add preservation picardZeroLineBundleClassification stability
    Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions hA hB f g

end Langlands.AbelianScheme
