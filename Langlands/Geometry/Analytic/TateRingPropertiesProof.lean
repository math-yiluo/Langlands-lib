import Langlands.Geometry.Analytic.TateIntegralClosure
import Langlands.Geometry.Analytic.TateRingPropertiesStatement

/-! # Ring properties of actual strict Tate algebras -/

universe u

namespace Langlands.Analytic.StrictTateAlgebra

theorem tateRingProperties (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] : TateRingPropertiesStatement K :=
  fun n => ⟨isNoetherianRing_tate n, inferInstance,
    uniqueFactorization_tate n, isIntegrallyClosed_tate n⟩

end Langlands.Analytic.StrictTateAlgebra
