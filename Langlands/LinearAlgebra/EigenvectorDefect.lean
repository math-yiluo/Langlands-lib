import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Powers of an eigenvector defect

Shared algebraic helper for scalar-layer and central dual-to-primal arguments.
-/

namespace Langlands.ScalarLayer

/-- Powers of a character defect act on an eigenvector by the corresponding scalar. -/
theorem pow_sub_smul_apply_of_eigen {X : Type*} [AddCommGroup X] [Module ℂ X]
    (L : Module.End ℂ X) {x : X} {μ : ℂ} (hx : L x = μ • x) (c : ℂ) (k : ℕ) :
    ((L - c • 1) ^ k) x = (μ - c) ^ k • x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, hx, ← sub_smul, smul_smul, pow_succ]

end Langlands.ScalarLayer
