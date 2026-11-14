import Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelAssembly
import Langlands.GroupScheme.IntegralModel.MaximalBoundedConstruction

/-! # Smooth models of the maximal bounded unramified torus subgroup -/

universe u

namespace Langlands.BruhatTits.IntegralModels

/-- A smooth model over the maximal unramified integers whose integral-point
image is the common character-valuation kernel of the torus. -/
theorem unramifiedTorusBoundedModel : UnramifiedTorusBoundedModelStatement.{u} :=
  unramifiedTorusBoundedModelAssembly.{u}
    Langlands.GroupScheme.maximalBoundedIntegralModel.{u}

end Langlands.BruhatTits.IntegralModels
