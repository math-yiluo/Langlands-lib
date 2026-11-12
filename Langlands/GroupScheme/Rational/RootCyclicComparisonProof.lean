import Langlands.GroupScheme.Rational.RootCyclicComparisonReduction
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.RootSubgroupUniquenessProof

/-! # Cyclic comparison for actual relative roots -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- The exact published proposition, with its structural inputs discharged. -/
theorem actualRootCyclicComparison :
    ActualRootCyclicComparisonStatement.{u} :=
  actualRootCyclicComparison_of_realization_uniqueness
    semigroupRealization rootSubgroupUniqueness

end Langlands.GroupScheme.RelativeRoot
