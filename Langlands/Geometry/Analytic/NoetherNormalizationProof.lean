import Langlands.Geometry.Analytic.NoetherNormalization
import Langlands.Geometry.Analytic.NoetherNormalizationStatement

/-! # Constructed normalization of strict affinoid quotients -/

universe u

namespace Langlands.Analytic.PresentedStrictAffinoidAlgebra

theorem noetherNormalization (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : NoetherNormalizationStatement K := by
  intro A hA
  let := hA
  exact exists_noetherNormalization A

end Langlands.Analytic.PresentedStrictAffinoidAlgebra
