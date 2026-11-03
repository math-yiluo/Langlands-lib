import Langlands.GroupScheme.Absolute.SolvableSubgroupBorelContainmentStatement
import Langlands.GroupScheme.Absolute.BorelContaining

/-! # Proof that a Borel contains each given smooth connected solvable subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every given smooth connected solvable closed subgroup of a smooth affine connected group
over an algebraically closed field factors through an actual Borel subgroup. The given
embedding is admissible, so the restricted height minimization of
`BorelExistence.exists_isBorelSubgroup_containing` applies to it. -/
theorem solvableSubgroupBorelContainment :
    SolvableSubgroupBorelContainmentStatement.{u} := by
  intro k _ _ G _ _ _ H j _ _ hj hH
  exact BorelExistence.exists_isBorelSubgroup_containing j
    ⟨hj, inferInstance, inferInstance, hH⟩

end Langlands.GroupScheme
