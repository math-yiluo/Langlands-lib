import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Every square matrix over a field is conjugate to its transpose

This is the matrix fact quoted as condition d) in Bernstein–Zelevinsky (1976),
§7.3: "Transposed matrices are conjugate in G."
-/

namespace Langlands

universe uK

/-- Every square matrix over a field is conjugate to its transpose by an
invertible matrix over the same field. -/
def MatrixTransposeConjugateStatement : Prop :=
  ∀ (K : Type uK) [Field K] (n : ℕ) (x : Matrix (Fin n) (Fin n) K),
    ∃ g : Matrix.GeneralLinearGroup (Fin n) K,
      (g : Matrix (Fin n) (Fin n) K) * x *
          ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = x.transpose

end Langlands
