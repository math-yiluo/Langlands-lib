import Langlands.Representation.RankinSelberg.SymmetricAlternantBridge

/-! # Elementary Pieri identities for Jacobi–Trudi polynomials -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

open MvPolynomial

/-- Add one to the coordinates selected by a finite subset. -/
def raiseWeight {m : ℕ} (α : Fin m → ℤ) (s : Finset (Fin m)) : Fin m → ℤ :=
  fun i => α i + if i ∈ s then 1 else 0

variable {R : Type*} [CommRing R]

theorem raiseWeight_nonneg {m : ℕ} (α : Fin m → ℤ) (hα : ∀ i, 0 ≤ α i)
    (s : Finset (Fin m)) : ∀ i, 0 ≤ raiseWeight α s i := by
  intro i
  have := hα i
  by_cases hi : i ∈ s <;> simp only [raiseWeight, hi, ite_true, ite_false] <;> omega

/-- Raising selected exponents is the column-scaled row selection in the alternant. -/
theorem alternantMatrix_raiseWeight {n : ℕ} (α : Fin (n + 1) → ℤ)
    (hα : ∀ i, 0 ≤ α i) (s : Finset (Fin (n + 1))) :
    alternantMatrix R (raiseWeight α s) =
      selectRows (alternantMatrix R α)
        (Matrix.of fun i j => alternantMatrix R α i j * X j) s := by
  apply Matrix.ext
  intro i j
  by_cases hi : i ∈ s
  · have he : (α i + 1 - i + n).toNat = (α i - i + n).toNat + 1 := by
      have := hα i
      have := i.isLt
      omega
    simp only [alternantMatrix, raiseWeight, selectRows, Matrix.of_apply, hi,
      ite_true, he, pow_succ]
  · simp [alternantMatrix, raiseWeight, selectRows, hi]

/-- The elementary Pieri identity before removal of the zero nondominant terms. -/
theorem jacobiTrudi_mul_esymm [IsDomain R] {n : ℕ} (α : Fin (n + 1) → ℤ)
    (hα : ∀ i, 0 ≤ α i) (k : ℕ) :
    jacobiTrudi R α * esymm (Fin (n + 1)) R k =
      ∑ s ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
        jacobiTrudi R (raiseWeight α s) := by
  let D := Matrix.det (alternantMatrix R (0 : Fin (n + 1) → ℤ))
  have hD : D ≠ 0 := by
    dsimp [D]
    rw [← det_erasedCoefficientMatrix]
    exact det_erasedCoefficientMatrix_ne_zero n
  apply mul_right_cancel₀ hD
  calc
    (jacobiTrudi R α * esymm (Fin (n + 1)) R k) * D =
        Matrix.det (alternantMatrix R α) * esymm (Fin (n + 1)) R k := by
      rw [← jacobiTrudi_mul_baseAlternant α hα]
      dsimp [D]
      ring
    _ = ∑ s ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
        Matrix.det (alternantMatrix R (raiseWeight α s)) := by
      simp_rw [alternantMatrix_raiseWeight α hα]
      exact (sum_det_column_scaled (alternantMatrix R α)
        (fun j => (X j : MvPolynomial (Fin (n + 1)) R)) k).symm
    _ = (∑ s ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
        jacobiTrudi R (raiseWeight α s)) * D := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      exact (jacobiTrudi_mul_baseAlternant (raiseWeight α s)
        (raiseWeight_nonneg α hα s)).symm

end Langlands.GeneralLinear.Spherical
