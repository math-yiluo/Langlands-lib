import Langlands.Representation.RankinSelberg.SymmetricDeterminantIdentities
import Mathlib.LinearAlgebra.Vandermonde

/-! # The complete symmetric convolution and alternant bridge -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

open MvPolynomial

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

/-- Remove the factor indexed by `k` from the elementary generating product. -/
def erasedElementaryProduct (k : σ) : PowerSeries (MvPolynomial σ R) :=
  ∏ i ∈ (Finset.univ : Finset σ).erase k,
    (1 - PowerSeries.C (X i : MvPolynomial σ R) * PowerSeries.X)

/-- Multiplying by the erased elementary product leaves one geometric series. -/
theorem completeSeries_mul_erasedElementaryProduct (k : σ) :
    completeSeries σ R * erasedElementaryProduct (R := R) k =
      PowerSeries.mk (fun n : ℕ => (X k : MvPolynomial σ R) ^ n) := by
  let g : PowerSeries (MvPolynomial σ R) := PowerSeries.mk (fun n : ℕ => X k ^ n)
  let l : PowerSeries (MvPolynomial σ R) := 1 - PowerSeries.C (X k) * PowerSeries.X
  have hgl : g * l = 1 := by
    have h := congrArg (PowerSeries.rescale (X k : MvPolynomial σ R))
      (PowerSeries.mk_one_mul_one_sub_eq_one (MvPolynomial σ R))
    simpa [g, l, PowerSeries.rescale_mk, smul_eq_mul] using h
  have hprod : erasedElementaryProduct (R := R) k * l =
      ∏ i : σ, (1 - PowerSeries.C (X i : MvPolynomial σ R) * PowerSeries.X) := by
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ k)
  change completeSeries σ R * erasedElementaryProduct k = g
  calc
    _ = (completeSeries σ R * erasedElementaryProduct k) * (l * g) := by
      rw [mul_comm l g, hgl, mul_one]
    _ = (completeSeries σ R * (erasedElementaryProduct k * l)) * g := by ring
    _ = g := by rw [hprod, completeSeries_mul_elementaryProduct, one_mul]

/-- The erased elementary product has no coefficients in degree at least the rank. -/
theorem coeff_erasedElementaryProduct_eq_zero (k : σ) (n : ℕ)
    (hn : Fintype.card σ ≤ n) :
    PowerSeries.coeff n (erasedElementaryProduct (R := R) k) = 0 := by
  unfold erasedElementaryProduct
  have hlinear (i : σ) :
      1 - PowerSeries.C (X i : MvPolynomial σ R) * PowerSeries.X =
        1 + PowerSeries.C (-X i) * PowerSeries.X := by simp [sub_eq_add_neg]
  simp_rw [hlinear]
  rw [coeff_prod_linear]
  have hcard : ((Finset.univ : Finset σ).erase k).card < n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ]
    have : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr ⟨k⟩
    omega
  rw [Finset.powersetCard_eq_empty.mpr hcard, Finset.sum_empty]

/-- Extract a finite convolution using the zero convention in negative degree. -/
theorem sum_completeSymm_coeff (Q : PowerSeries (MvPolynomial σ R)) (m n : ℕ)
    (hQ : ∀ j, m ≤ j → PowerSeries.coeff j Q = 0) :
    (∑ j ∈ Finset.range m,
      completeSymm σ R ((n : ℤ) - j) * PowerSeries.coeff j Q) =
      PowerSeries.coeff n (completeSeries σ R * Q) := by
  have hcoeff : PowerSeries.coeff n (completeSeries σ R * Q) =
      ∑ j ∈ Finset.range (n + 1),
        completeSymm σ R ((n : ℤ) - j) * PowerSeries.coeff j Q := by
    rw [mul_comm, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
    simp only [completeSeries, PowerSeries.coeff_mk]
    rw [completeSymm, ite_eq_left (by omega)]
    have hnat : ((n : ℤ) - j).toNat = n - j := by omega
    rw [hnat]
    simp [mul_comm]
  rw [hcoeff]
  by_cases hmn : m ≤ n + 1
  · apply Finset.sum_subset (Finset.range_mono hmn)
    intro j _ hj
    rw [hQ j (by simpa using hj), mul_zero]
  · symm
    apply Finset.sum_subset (Finset.range_mono (Nat.le_of_lt (Nat.lt_of_not_ge hmn)))
    intro j _ hj
    have hjn : n < j := by simpa using hj
    rw [completeSymm, ite_eq_right (by omega), zero_mul]

/-- The finite convolution in the reversed column order of Jacobi–Trudi. -/
theorem sum_completeSymm_erased (n : ℕ) (r : ℤ) (hr : 0 ≤ r + n)
    (k : Fin (n + 1)) :
    (∑ j : Fin (n + 1), completeSymm (Fin (n + 1)) R (r + j) *
      PowerSeries.coeff j.rev.val (erasedElementaryProduct (R := R) k)) =
      (X k : MvPolynomial (Fin (n + 1)) R) ^ (r + n).toNat := by
  have h := sum_completeSymm_coeff (erasedElementaryProduct (R := R) k)
    (n + 1) (r + n).toNat (fun j hj =>
      coeff_erasedElementaryProduct_eq_zero k j (by simpa using hj))
  rw [completeSeries_mul_erasedElementaryProduct, PowerSeries.coeff_mk] at h
  rw [← h, ← Fin.sum_univ_eq_sum_range]
  conv_lhs => rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  have he : r + (j.rev.val : ℤ) = ((r + n).toNat : ℤ) - j.val := by
    have hj := j.add_rev_cast
    rw [Int.toNat_of_nonneg hr]
    omega
  rw [he]

/-- The matrix whose determinant defines the published Jacobi–Trudi polynomial. -/
def jacobiTrudiMatrix (R : Type*) [CommRing R] {m : ℕ} (α : Fin m → ℤ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin m) R) :=
  Matrix.of fun i j => completeSymm (Fin m) R (α i - i + j)

/-- Coefficients of the erased elementary products, in reversed degree order. -/
def erasedCoefficientMatrix (R : Type*) [CommRing R] (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) R) :=
  Matrix.of fun j k =>
    PowerSeries.coeff j.rev.val (erasedElementaryProduct (R := R) k)

/-- The monomial matrix associated to an integral weight. -/
def alternantMatrix (R : Type*) [CommRing R] {n : ℕ} (α : Fin (n + 1) → ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) R) :=
  Matrix.of fun i k => X k ^ (α i - i + n).toNat

/-- Multiplication by the coefficient matrix converts Jacobi–Trudi to monomials. -/
theorem jacobiTrudiMatrix_mul_erased {n : ℕ} (α : Fin (n + 1) → ℤ)
    (hα : ∀ i, 0 ≤ α i) :
    jacobiTrudiMatrix R α * erasedCoefficientMatrix R n = alternantMatrix R α := by
  apply Matrix.ext
  intro i k
  exact sum_completeSymm_erased n (α i - i) (by have hi := i.isLt; have := hα i; omega) k

/-- At weight zero the coefficient determinant is the base alternant. -/
theorem det_erasedCoefficientMatrix (n : ℕ) :
    Matrix.det (erasedCoefficientMatrix R n) =
      Matrix.det (alternantMatrix R (0 : Fin (n + 1) → ℤ)) := by
  have h := congrArg Matrix.det (jacobiTrudiMatrix_mul_erased (R := R)
    (0 : Fin (n + 1) → ℤ) (fun _ => le_rfl))
  rw [Matrix.det_mul] at h
  change jacobiTrudi R (0 : Fin (n + 1) → ℤ) * _ = _ at h
  simpa only [jacobiTrudi_zero, one_mul] using h

/-- The base alternant is a row reversal of the transposed Vandermonde matrix. -/
theorem alternantMatrix_zero (n : ℕ) :
    alternantMatrix R (0 : Fin (n + 1) → ℤ) =
      (Matrix.vandermonde (fun k : Fin (n + 1) => (X k : MvPolynomial (Fin (n + 1)) R))).transpose.submatrix
        Fin.revPerm id := by
  apply Matrix.ext
  intro i k
  simp only [alternantMatrix, Matrix.of_apply, Pi.zero_apply, zero_sub,
    Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.vandermonde,
    Fin.revPerm_apply, id_eq]
  congr 1
  have hi := i.add_rev_cast
  omega

/-- The generic coefficient matrix has nonzero determinant. -/
theorem det_erasedCoefficientMatrix_ne_zero [IsDomain R] (n : ℕ) :
    Matrix.det (erasedCoefficientMatrix R n) ≠ 0 := by
  rw [det_erasedCoefficientMatrix, alternantMatrix_zero, Matrix.det_permute,
    Matrix.det_transpose]
  exact mul_ne_zero
    (((Equiv.Perm.sign Fin.revPerm).isUnit.map
      (Int.castRingHom (MvPolynomial (Fin (n + 1)) R))).ne_zero)
    (Matrix.det_vandermonde_ne_zero_iff.mpr MvPolynomial.X_injective)

/-- Cross-multiplied bialternant identity, including coinciding specializations. -/
theorem jacobiTrudi_mul_baseAlternant {n : ℕ} (α : Fin (n + 1) → ℤ)
    (hα : ∀ i, 0 ≤ α i) :
    jacobiTrudi R α * Matrix.det (alternantMatrix R (0 : Fin (n + 1) → ℤ)) =
      Matrix.det (alternantMatrix R α) := by
  rw [← det_erasedCoefficientMatrix]
  exact (Matrix.det_mul _ _).symm.trans
    (congrArg Matrix.det (jacobiTrudiMatrix_mul_erased α hα))

end Langlands.GeneralLinear.Spherical
