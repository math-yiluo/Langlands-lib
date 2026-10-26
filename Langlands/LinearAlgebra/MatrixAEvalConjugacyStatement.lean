import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Polynomial-module isomorphisms give matrix conjugacy -/

namespace Langlands

universe uK

/-- A polynomial-linear isomorphism between the modules on which `X` acts by
`x` and `y` gives a matrix conjugating `x` to `y`. -/
def MatrixAEvalConjugacyStatement : Prop :=
  ∀ (K : Type uK) [Field K] (n : ℕ) (x y : Matrix (Fin n) (Fin n) K),
    (Module.AEval' x.mulVecLin ≃ₗ[Polynomial K] Module.AEval' y.mulVecLin) →
      ∃ g : Matrix.GeneralLinearGroup (Fin n) K,
        (g : Matrix (Fin n) (Fin n) K) * x *
          ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = y

end Langlands
