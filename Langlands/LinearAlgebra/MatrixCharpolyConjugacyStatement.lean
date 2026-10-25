import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Finitely many conjugacy classes with a given characteristic polynomial

The finiteness that makes conjugation constructive along the fibers of the
characteristic-polynomial map; compare Bernstein–Zelevinsky (1976), Remark 7.4.
-/

namespace Langlands

universe uK

/-- Over a field, the square matrices of fixed size with a prescribed
characteristic polynomial fall into finitely many conjugacy classes: some finite
set of matrices meets the conjugacy class of each of them. -/
def MatrixCharpolyFiniteConjugacyStatement : Prop :=
  ∀ (K : Type uK) [Field K] (n : ℕ) (c : Polynomial K),
    ∃ s : Finset (Matrix (Fin n) (Fin n) K),
      ∀ x : Matrix (Fin n) (Fin n) K, x.charpoly = c →
        ∃ y ∈ s, ∃ g : Matrix.GeneralLinearGroup (Fin n) K,
          (g : Matrix (Fin n) (Fin n) K) * x *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = y

end Langlands
