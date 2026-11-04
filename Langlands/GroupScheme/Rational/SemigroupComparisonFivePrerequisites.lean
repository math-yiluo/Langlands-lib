import Langlands.GroupScheme.Reductive.NormalCenterDescent
import Langlands.GroupScheme.Rational.SemigroupComparisonSixPrerequisites

/-! # Semigroup comparison from five structural prerequisites -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- The remaining structural inputs to the full semigroup comparison. Full-centre
containment and radical intersection are consequences of the fixed-torus input. -/
def SemigroupComparisonPrerequisites : Prop :=
  AdjointQuotientExistenceStatement.{u} ∧
    FixedCenterContainingTorusStatement.{u} ∧
    SemigroupAdjointImageStatement.{u} ∧
    NormalAdjointEquivariantRetractionStatement.{u} ∧
    Torus.SolvableFixedContainmentConnectedStatement.{u}

/-- The first four retained inputs give the former normal reductive bundle,
because the fixed-torus input also gives full-centre containment. -/
theorem SemigroupComparisonPrerequisites.normalReductive
    (h : SemigroupComparisonPrerequisites.{u}) :
    NormalReductiveSemigroupPrerequisites.{u} :=
  ⟨h.1, h.2.1, normalReductiveCenter_of_fixedCenterContainingTorus h.2.1,
    h.2.2.1, h.2.2.2.1⟩

/-- The five retained structural propositions imply the exact existing full
comparison, with every field, universe and all three intersection alternatives. -/
theorem semigroupComparison_of_fivePrerequisites
    (h : SemigroupComparisonPrerequisites.{u}) :
    SemigroupComparisonStatement.{u} :=
  semigroupComparison_of_reductive_and_solvablePrerequisites
    h.normalReductive h.2.2.2.2

end Langlands.GroupScheme.RelativeRoot
