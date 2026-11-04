import Langlands.GroupScheme.Rational.SemigroupComparisonReduction
import Langlands.GroupScheme.Reductive.NormalUnipotentRadicalIntersectionReduction

/-! # Semigroup comparison from the reductive and solvable prerequisites -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- The five normal-reductive structural inputs and the solvable connectedness
input imply the exact full comparison. Radical intersection follows from the
already retained fixed centre-containing torus input. -/
theorem semigroupComparison_of_reductive_and_solvablePrerequisites
    (hReductive : NormalReductiveSemigroupPrerequisites.{u})
    (hSolvable : Torus.SolvableFixedContainmentConnectedStatement.{u}) :
    SemigroupComparisonStatement.{u} :=
  semigroupComparison_of_structuralPrerequisites
    ⟨normalUnipotentRadicalIntersection_of_fixedCenterContainingTorus hReductive.2.1,
      hReductive, hSolvable⟩

end Langlands.GroupScheme.RelativeRoot
