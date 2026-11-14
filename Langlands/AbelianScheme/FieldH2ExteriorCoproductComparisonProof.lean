import Langlands.AbelianScheme.CanonicalCAR
import Langlands.AbelianScheme.FieldStructureSheafH1DimensionProof

/-! # The degree-two exterior and canonical coproduct comparison -/

universe u

namespace Langlands.AbelianScheme

/-- The actual degree-two structure-sheaf cohomology of an abelian variety has simultaneous
exterior and product comparisons compatible with both projections and multiplication. -/
theorem fieldH2ExteriorCoproductComparison :
    FieldH2ExteriorCoproductComparisonStatement.{u} :=
  fieldH2ExteriorCoproductComparison_of_H1Dimension fieldStructureSheafH1Dimension

end Langlands.AbelianScheme
