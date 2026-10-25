import Langlands.GroupTheory.CyclicHerbrandStatement
import Langlands.Cohomology.HerbrandQuotient

/-! # Proof of the cyclic Herbrand calculus for ordinary group cohomology -/

namespace Langlands.GroupTheory

universe u

open CategoryTheory Langlands.Cohomology.Herbrand

/-- The three two-out-of-three cases of division-free Herbrand multiplicativity. -/
theorem cyclicHerbrandShortExact : CyclicHerbrandShortExact.{u} := by
  intro k G _ _ _ _ S hS
  refine ⟨fun h₁ h₂ h₃ h₄ => ?_, fun h₁ h₂ h₃ h₄ => ?_, fun h₁ h₂ h₃ h₄ => ?_⟩
  · have := h₁; have := h₂; have := h₃; have := h₄
    exact natCard_of_shortExact_mid hS
  · have := h₁; have := h₂; have := h₃; have := h₄
    exact natCard_of_shortExact_left hS
  · have := h₁; have := h₂; have := h₃; have := h₄
    exact natCard_of_shortExact_right hS

/-- Finite coefficients have finite `H¹` and `H²` of equal cardinality. -/
theorem cyclicHerbrandFiniteCoefficients : CyclicHerbrandFiniteCoefficients.{u} := by
  intro k G _ _ _ _ V _
  exact natCard_two_eq_natCard_one_of_finite V

/-- For trivial integers, `H¹` is trivial and `H²` is finite of order `|G|`. -/
theorem cyclicHerbrandTrivialIntegers : CyclicHerbrandTrivialIntegers.{u} := by
  intro G _ _ _
  exact groupCohomology_trivialIntegers

/-- The cyclic Herbrand calculus for ordinary group cohomology. -/
theorem cyclicHerbrandCalculus : CyclicHerbrandCalculus.{u} :=
  ⟨cyclicHerbrandShortExact, cyclicHerbrandFiniteCoefficients, cyclicHerbrandTrivialIntegers⟩

end Langlands.GroupTheory
