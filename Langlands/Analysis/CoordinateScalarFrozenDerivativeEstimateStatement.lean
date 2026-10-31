import Langlands.Analysis.CoordinateScalarDifferentialOperator
import Langlands.Analysis.OrderedDerivativeFamilyNorm

/-! # Differentiating a frozen principal scalar action -/

noncomputable section
open scoped BigOperators ContDiff
set_option autoImplicit false

namespace Langlands.Analysis

universe uE

/-- The actual frozen principal action is bounded by the full action, a small
top-coefficient variation term, and strictly lower total derivatives. -/
def CoordinateScalarFrozenDerivativeEstimateStatement
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E] (d r : ℕ) : Prop :=
  ∀ (D : CoordinateScalarOperator E d r),
    let v : Fin d → E := fun i => D.basis i
    let T : ℕ → (E → ℂ) → E → ℝ :=
      fun q f y => orderedDerivativeFamilyNorm v q (fun _ : Unit => f) y
    ∀ (S : Set E), IsOpen S →
      (∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d),
        ContDiffOn ℝ ∞ (D.coefficient k w) S) →
      ∀ u : E → ℂ, ContDiffOn ℝ ∞ u S →
        ∀ (x₀ : E) (p : ℕ) (x : E), x ∈ S →
          T p (fun y => ∑ w : Fin r → Fin d,
              D.coefficient (Fin.last r) w x₀ *
                iteratedFDeriv ℝ r u y (v ∘ w)) x ≤
            T p (D.action u) x +
              (∑ w : Fin r → Fin d,
                ‖D.coefficient (Fin.last r) w x₀ - D.coefficient (Fin.last r) w x‖) *
                T (p + r) u x +
              (∑ w : Fin r → Fin d, ∑ j ∈ Finset.range p,
                (p.choose (j + 1) : ℝ) * T (j + 1) (D.coefficient (Fin.last r) w) x *
                  T (p - (j + 1) + r) u x) +
              ∑ k : Fin r, ∑ w : Fin k.val → Fin d,
                ∑ j ∈ Finset.range (p + 1),
                  (p.choose j : ℝ) * T j (D.coefficient k.castSucc w) x *
                    T (p - j + k.val) u x

end Langlands.Analysis
