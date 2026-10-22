import Mathlib.Analysis.Normed.Ring.Basic

/-! # Bounded powers in a normed ring -/

universe u

namespace Langlands.Analytic

/-- A single positive real constant bounds every nonnegative integral power. -/
def HasBoundedPowers {A : Type u} [NormedRing A] (a : A) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C

end Langlands.Analytic
