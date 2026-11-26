import Langlands.LocalFactor.Ramification.Herbrand.LocalAbsoluteContinuityProof
import Langlands.LocalFactor.Ramification.Herbrand.LocalAbsoluteImageProof
import Langlands.LocalFactor.Ramification.Herbrand.LocalAbsoluteInertiaProof
import Langlands.LocalFactor.Ramification.Wintenberger.Absolute

namespace Langlands.Ramification.Local

universe uK uΩ

/-- The five properties of the absolute upper filtration for every nonarchimedean
local field and every separable closure, in independent universes. -/
theorem absoluteHerbrandArithmetic : AbsoluteHerbrandArithmetic.{uK, uΩ} := by
  intro K _ _ _ _ Ω _ _ _
  exact ⟨Wintenberger.localAbsoluteUpperFiniteImage K Ω, absoluteUpperInertia K Ω,
    absoluteUpperLeftContinuity K Ω, absoluteUpperClosedRightImage K Ω,
    absoluteUpperWildInertia K Ω⟩

end Langlands.Ramification.Local
