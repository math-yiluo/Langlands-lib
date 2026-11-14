import Langlands.AbelianScheme.FieldH2ExteriorCoproductComparisonProof

/-! # Injectivity of the degree-two reduced coproduct -/

universe u

namespace Langlands.AbelianScheme

/-- Multiplication pullback minus the two projection pullbacks is injective on the
actual structure-sheaf cohomology in degree two over every field. -/
theorem fieldH2PrimitiveInjectivity : FieldH2PrimitiveInjectivityStatement.{u} :=
  fieldH2PrimitiveInjectivity_of_exteriorCoproductComparison
    fieldH2ExteriorCoproductComparison

end Langlands.AbelianScheme
