import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

/-!
# The exterior square of a `4 × 4` matrix

For a `4 × 4` matrix `M` over a commutative ring, `ExteriorSquare.matrix M` is the `6 × 6`
matrix of `Λ² M` in the basis `e₀∧e₁, e₀∧e₂, e₀∧e₃, e₁∧e₂, e₁∧e₃, e₂∧e₃`: its entries are the
`2 × 2` minors of `M`. It is multiplicative, and it preserves the symmetric wedge pairing
`(ξ, η) ↦ ξ ∧ η ∈ Λ⁴ A⁴ = A` (Gram matrix `pfaffian`) up to the factor `det M`. Only this bilinear
pairing is treated. The split Pfaffian quadratic form `q = x₀₁ x₂₃ - x₀₂ x₁₃ + x₀₃ x₁₂` satisfies
`ξ ∧ ξ = 2 q(ξ)`, so the bilinear identities here say nothing about `q` in characteristic two.
-/

namespace Langlands.GroupScheme.ExteriorSquare

variable {A : Type*} [CommRing A]

/-- The six increasing pairs of `Fin 4`, in lexicographic order. -/
def pair : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The exterior square: the matrix of `2 × 2` minors. -/
def matrix (M : Matrix (Fin 4) (Fin 4) A) : Matrix (Fin 6) (Fin 6) A :=
  Matrix.of fun I J =>
    M (pair I).1 (pair J).1 * M (pair I).2 (pair J).2 -
      M (pair I).1 (pair J).2 * M (pair I).2 (pair J).1

/-- The Gram matrix of the symmetric wedge pairing `ξ ∧ η = B(ξ, η) e₀∧e₁∧e₂∧e₃`. -/
def pfaffian : Matrix (Fin 6) (Fin 6) A :=
  Matrix.of ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0], ![0, -1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]

theorem matrix_apply (M : Matrix (Fin 4) (Fin 4) A) (I J : Fin 6) :
    matrix M I J = M (pair I).1 (pair J).1 * M (pair I).2 (pair J).2 -
      M (pair I).1 (pair J).2 * M (pair I).2 (pair J).1 := rfl

theorem matrix_mul (M N : Matrix (Fin 4) (Fin 4) A) :
    matrix (M * N) = matrix M * matrix N := by
  ext I J
  fin_cases I <;> fin_cases J <;>
    simp [matrix_apply, pair, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_six] <;> ring

theorem matrix_one : matrix (1 : Matrix (Fin 4) (Fin 4) A) = 1 := by
  ext I J
  fin_cases I <;> fin_cases J <;> simp [matrix_apply, pair, Matrix.one_apply]

theorem matrix_transpose (M : Matrix (Fin 4) (Fin 4) A) :
    matrix M.transpose = (matrix M).transpose := by
  ext I J
  simp only [matrix_apply, Matrix.transpose_apply]
  ring

theorem matrix_map {B : Type*} [CommRing B] (f : A →+* B) (M : Matrix (Fin 4) (Fin 4) A) :
    matrix (M.map f) = (matrix M).map f := by
  ext I J
  simp [matrix_apply]

theorem pfaffian_mul_self : (pfaffian : Matrix (Fin 6) (Fin 6) A) * pfaffian = 1 := by
  ext I J
  fin_cases I <;> fin_cases J <;>
    simp [pfaffian, Matrix.mul_apply, Fin.sum_univ_six]

theorem pfaffian_transpose : (pfaffian : Matrix (Fin 6) (Fin 6) A).transpose = pfaffian := by
  ext I J
  fin_cases I <;> fin_cases J <;> simp [pfaffian]

theorem det_fin_four (M : Matrix (Fin 4) (Fin 4) A) :
    M.det =
      M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) - M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) +
          M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)) -
        M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
          M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)) +
        M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) -
          M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) -
        M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) -
          M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0) + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [Fin.succAbove, Fin.lt_def, pow_succ]
  ring

/-- The exterior square multiplies the wedge pairing by the determinant. -/
theorem transpose_mul_pfaffian_mul (M : Matrix (Fin 4) (Fin 4) A) :
    (matrix M).transpose * pfaffian * matrix M = M.det • pfaffian := by
  rw [det_fin_four]
  ext I J
  fin_cases I <;> fin_cases J <;>
    simp [matrix_apply, pair, pfaffian, Matrix.mul_apply, Fin.sum_univ_six] <;> ring

/-- The same identity on the other side. -/
theorem mul_pfaffian_mul_transpose (M : Matrix (Fin 4) (Fin 4) A) :
    matrix M * pfaffian * (matrix M).transpose = M.det • pfaffian := by
  have h := transpose_mul_pfaffian_mul M.transpose
  rwa [matrix_transpose, Matrix.transpose_transpose, Matrix.det_transpose] at h

end Langlands.GroupScheme.ExteriorSquare
