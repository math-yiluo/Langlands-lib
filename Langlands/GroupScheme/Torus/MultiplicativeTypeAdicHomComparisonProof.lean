import Langlands.GroupScheme.HomScheme.AdicDiagonalizable
import Langlands.GroupScheme.Torus.MultiplicativeTypeAdicHomDescentProof

/-! # Adic Hom comparison for isotrivial groups of multiplicative type -/

universe u

namespace Langlands.GroupScheme

/-- SGA 3, Exposé IX, Théorème 7.1 for the Library's finite-type diagonalizable
groups. Restriction to the adic tower is bijective for isotrivial sources and
affine targets. -/
theorem multiplicativeTypeAdicHomComparison :
    MultiplicativeTypeAdicHomComparisonStatement.{u} := by
  apply multiplicativeTypeAdicHomDescent
  intro A _ _ I _ H G _ hH
  exact HomScheme.AdicDiagonalizable.restrict_bijective_of_isDiagonalizable I H G hH

end Langlands.GroupScheme
