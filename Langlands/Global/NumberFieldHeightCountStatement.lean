import Mathlib.NumberTheory.Height.NumberField

universe u

namespace Langlands.Global

/-- In a number field the number of elements of multiplicative height at most
`B` is bounded by a constant times a fixed power of `B`, for every `B ≥ 1`. -/
def NumberFieldMulHeightCountStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    ∃ (C : ℝ) (M : ℕ), ∀ B : ℝ, 1 ≤ B →
      ({x : K | Height.mulHeight₁ x ≤ B}.ncard : ℝ) ≤ C * B ^ M

end Langlands.Global
