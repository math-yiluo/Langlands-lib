import Langlands.BushnellKutzko.MinimalCriticalExponentStatement
import Langlands.BushnellKutzko.MinimalCriticalExponent.CriticalExponentReduction
import Langlands.BushnellKutzko.MinimalityAtAdjointStep

/-! # The critical exponent and minimality (Bushnell–Kutzko (1.4.15)) -/

namespace Langlands.BushnellKutzko

universe uF uV uE

/-- The critical exponent is finite and bounds the order valuation, with equality
exactly for minimal generators. -/
theorem minimalCriticalExponent : MinimalCriticalExponentStatement.{uF,uV,uE} := by
  intro F _ _ _ _ V _ _ _ E _ _ _ _ 𝓛 β hgen hscalar hnormal
  have hβ : β ≠ 0 := fun h => hscalar ⟨0, (map_zero (algebraMap F E)).trans h.symm⟩
  let u := Units.mk0 β hβ
  obtain ⟨k₀, hk₀, hle, heq⟩ := criticalExponent_ge_shift_and_eq_iff 𝓛 hnormal u hgen hscalar
  have hmin := minimalityAtAdjointStep F V E 𝓛 hnormal u hgen
  exact ⟨k₀, hk₀, hle, heq.trans hmin.symm⟩

end Langlands.BushnellKutzko
