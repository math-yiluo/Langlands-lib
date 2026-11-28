import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Basic

/-! # Rapid polynomial approximation in real coordinates -/

open scoped ContDiff

set_option autoImplicit false

namespace Langlands.Analysis

universe u v

/-- Scalar-valued smooth families on a real box admit polynomial approximation at every
power rate, uniformly on a compact set of auxiliary parameters. -/
def SmoothCoordinatePolynomialApproximationStatement : Prop :=
  ∀ (J : Type u) [Fintype J] (Y : Type v) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (S : Set Y), IsCompact S → ∀ (r : ℝ), 0 < r →
    ∀ (F : (J → ℝ) × Y → ℂ), ContDiff ℝ ∞ F → ∀ q : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ → Y → MvPolynomial J ℂ,
      (∀ m y, (P m y).totalDegree ≤ Fintype.card J * m) ∧
      ∀ m y, y ∈ S → ∀ x : J → ℝ, (∀ j, |x j| ≤ r) →
        ‖F (x, y) - (P m y).eval (fun i => (x i : ℂ))‖ ≤ C / ((m : ℝ) + 1) ^ q

end Langlands.Analysis
