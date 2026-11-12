import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalFieldProperPointValuativeReductionStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalFieldProperPointLimit

/-! # Corollary 5.6 for algebraic spaces from the valuative criterion: proof -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The valuative existence criterion implies Conrad's Corollary 5.6 for algebraic spaces. -/
theorem localFieldProperPointValuativeReduction :
    LocalFieldProperPointValuativeReductionStatement.{u} :=
  LocalFieldProperPointLimit.localFieldProperPointMap_of_valuative

end Langlands.AlgebraicGeometry.AlgebraicSpace
