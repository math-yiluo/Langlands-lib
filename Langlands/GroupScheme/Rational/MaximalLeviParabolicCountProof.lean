import Langlands.Representation.Geometric.MaximalLeviParabolicBudget

/-! # The actual maximal-Levi parabolic count and its geometric application -/

universe u

namespace Langlands.GroupScheme

/-- At most two distinct actual rational parabolic images share a maximal Levi. -/
theorem maximalLeviParabolicCount : MaximalLeviParabolicCountStatement.{u} :=
  maximalLeviParabolicCount_core

end Langlands.GroupScheme
