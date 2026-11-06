import Langlands.GroupScheme.Rational.RootSignUnipotentInclusion
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # The all-test nested semistandard parabolic decomposition -/

universe u

namespace Langlands.GroupScheme

/-- Compatible nested dynamic parabolics in a connected reductive group have nested Levi
decompositions: the conditional reduction from relative-root negation, discharged by the
unconditional negation theorem. -/
theorem dynamicNestedParabolicDecomposition :
    DynamicNestedParabolicDecompositionStatement.{u} :=
  dynamicNestedParabolicDecomposition_of_negation relativeRootNegation

end Langlands.GroupScheme
