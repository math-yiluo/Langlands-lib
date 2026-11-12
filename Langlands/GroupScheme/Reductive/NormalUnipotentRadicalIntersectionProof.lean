import Langlands.GroupScheme.Reductive.NormalUnipotentRadicalIntersectionReduction
import Langlands.GroupScheme.Reductive.FixedCenterContainingTorusProof

/-! # Unipotent radicals of normal connected subgroups: proof -/

universe u

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, a smooth connected normal subgroup
meets the ambient unipotent radical in its own full unipotent radical, on
every test scheme. -/
theorem normalUnipotentRadicalIntersection :
    NormalUnipotentRadicalIntersectionStatement.{u} :=
  normalUnipotentRadicalIntersection_of_fixedCenterContainingTorus
    fixedCenterContainingTorus

end Langlands.GroupScheme
