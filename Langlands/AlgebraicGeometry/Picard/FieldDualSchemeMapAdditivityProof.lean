import Langlands.AlgebraicGeometry.Picard.DualSchemeMapAdditivity
import Langlands.AlgebraicGeometry.Picard.PicardZeroLineBundleClassificationProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-! # Additivity of the dual scheme maps over a field -/

universe u

namespace Langlands.AbelianScheme

/-- Over a field, dualization carries a sum of homomorphisms of abelian schemes to the
product of the dual maps under the constructed tensor multiplication on the dual. -/
theorem fieldDualSchemeMapAdditivity : FieldDualSchemeMapAdditivityStatement.{u} :=
  fieldDualSchemeMapAdditivity_of_classification picardZeroLineBundleClassification
    Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions

end Langlands.AbelianScheme
