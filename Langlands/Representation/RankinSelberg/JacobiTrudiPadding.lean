import Langlands.Representation.RankinSelberg.CompleteCauchySeries

/-! # Zero padding for Jacobi–Trudi in an independent alphabet -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

/-- Extend an integral weight by zero coordinates on the right. -/
def padWeight {m : ℕ} (α : Fin m → ℤ) (k : ℕ) : Fin (m + k) → ℤ :=
  Fin.addCases α (fun _ => 0)

variable (σ R : Type*) [Fintype σ] [DecidableEq σ] [CommRing R]

/-- The zero-weight determinant is one independently of its alphabet size. -/
theorem jacobiTrudiIn_zero (m : ℕ) : jacobiTrudiIn σ R (0 : Fin m → ℤ) = 1 := by
  rw [jacobiTrudiIn, Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [completeSymm, MvPolynomial.hsymm_zero]
  · intro i j hji
    have hlt : j.val < i.val := hji
    have hneg : ¬ (0 : ℤ) ≤ (0 : Fin m → ℤ) i - (i : ℤ) + j := by
      simp only [Pi.zero_apply]
      omega
    rw [Matrix.of_apply, completeSymm, ite_eq_right hneg]

/-- Appending zero parts does not change Jacobi–Trudi in the supplied alphabet. -/
theorem jacobiTrudiIn_padWeight {m : ℕ} (α : Fin m → ℤ) (k : ℕ) :
    jacobiTrudiIn σ R (padWeight α k) = jacobiTrudiIn σ R α := by
  let J : Matrix (Fin (m + k)) (Fin (m + k)) (MvPolynomial σ R) :=
    Matrix.of fun i j => completeSymm σ R (padWeight α k i - i + j)
  let A : Matrix (Fin m) (Fin m) (MvPolynomial σ R) :=
    Matrix.of fun i j => completeSymm σ R (α i - i + j)
  let D : Matrix (Fin k) (Fin k) (MvPolynomial σ R) :=
    Matrix.of fun i j => completeSymm σ R (0 - i + j)
  let U : Matrix (Fin m) (Fin k) (MvPolynomial σ R) :=
    J.submatrix (Fin.castAdd k) (Fin.natAdd m)
  have hblock : J.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks A U 0 D := by
    apply Matrix.ext
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [J, A, padWeight]
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j =>
        simp only [J, Matrix.submatrix_apply, finSumFinEquiv_apply_right,
          finSumFinEquiv_apply_left, Matrix.of_apply, padWeight, Fin.addCases_right,
          Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
        rw [completeSymm, ite_eq_right (by have hj := j.isLt; simp only [Fin.val_natAdd, Fin.val_castAdd]; omega)]
      | inr j =>
        simp only [J, D, Matrix.submatrix_apply, finSumFinEquiv_apply_right,
          Matrix.of_apply, padWeight, Fin.addCases_right, Matrix.fromBlocks_apply₂₂]
        congr 1
        simp only [Fin.val_natAdd, Nat.cast_add]
        ring
  change Matrix.det J = Matrix.det A
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv J, hblock,
    Matrix.det_fromBlocks_zero₂₁]
  change jacobiTrudiIn σ R α * jacobiTrudiIn σ R (0 : Fin k → ℤ) = jacobiTrudiIn σ R α
  rw [jacobiTrudiIn_zero, mul_one]

/-- The usual same-rank Jacobi–Trudi polynomial is the independent-alphabet construction. -/
theorem jacobiTrudi_eq_jacobiTrudiIn {m : ℕ} (α : Fin m → ℤ) :
    jacobiTrudi R α = jacobiTrudiIn (Fin m) R α := rfl

/-- In a larger alphabet, the full zero-padded determinant equals the smaller matrix. -/
theorem jacobiTrudi_padWeight {m : ℕ} (α : Fin m → ℤ) (k : ℕ) :
    jacobiTrudi R (padWeight α k) = jacobiTrudiIn (Fin (m + k)) R α := by
  exact jacobiTrudiIn_padWeight (Fin (m + k)) R α k

end Langlands.GeneralLinear.Spherical
