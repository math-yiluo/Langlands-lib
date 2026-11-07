import Langlands.Representation.RankinSelberg.PowerSeriesMinorExpansion

/-! # Coefficients of the monomial minors in the Cauchy expansion -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

variable {R : Type*} [CommRing R]

/-- The coefficient minor selected by a tuple of natural exponents. -/
def seriesCoefficientMinor {m : ℕ} (H : PowerSeries R) (e : Fin m → ℕ) :
    Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i j => seriesCoeff H ((e j : ℤ) - i.rev.val)

/-- The monomial minor selected by the same tuple of exponents. -/
def monomialMinor {m : ℕ} (y : Fin m → R) (e : Fin m → ℕ) :
    Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i j => y j ^ e i

/-- Each column in a truncated minor contributes its fixed formal parameter power. -/
theorem det_truncatedSeriesMatrix_minor {m : ℕ} (H : PowerSeries R) (L : ℕ)
    (e : Fin m → Fin (L + 1)) :
    Matrix.det ((truncatedSeriesMatrix H L).submatrix id e) =
      PowerSeries.C (Matrix.det (seriesCoefficientMinor H (fun i => (e i).val))) *
        PowerSeries.X ^ (∑ i, (e i).val) := by
  have hmat : (truncatedSeriesMatrix H L).submatrix id e =
      (seriesCoefficientMinor H (fun i => (e i).val)).map PowerSeries.C *
        Matrix.diagonal (fun i => (PowerSeries.X : PowerSeries R) ^ (e i).val) := by
    apply Matrix.ext
    intro i j
    simp [truncatedSeriesMatrix, seriesCoefficientMinor, Matrix.mul_diagonal,
      PowerSeries.monomial_eq_C_mul_X_pow]
  have hd : Matrix.det ((seriesCoefficientMinor H (fun i => (e i).val)).map PowerSeries.C) =
      PowerSeries.C (Matrix.det (seriesCoefficientMinor H (fun i => (e i).val))) :=
    ((PowerSeries.C : R →+* PowerSeries R).map_det _).symm
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal, hd, Finset.prod_pow_eq_pow_sum]

theorem det_constantPowerMatrix_minor {m : ℕ} (y : Fin m → R) (L : ℕ)
    (e : Fin m → Fin (L + 1)) :
    Matrix.det ((constantPowerMatrix y L).submatrix e id) =
      PowerSeries.C (Matrix.det (monomialMinor y (fun i => (e i).val))) := by
  exact ((PowerSeries.C : R →+* PowerSeries R).map_det
    (monomialMinor y (fun i => (e i).val))).symm

/-- A pair of minors contributes in exactly its total exponent degree. -/
theorem coeff_minor_product {m : ℕ} (H : PowerSeries R) (y : Fin m → R) (L n : ℕ)
    (e : Fin m → Fin (L + 1)) :
    PowerSeries.coeff n
      (Matrix.det ((truncatedSeriesMatrix H L).submatrix id e) *
        Matrix.det ((constantPowerMatrix y L).submatrix e id)) =
      if n = ∑ i, (e i).val then
        Matrix.det (seriesCoefficientMinor H (fun i => (e i).val)) *
          Matrix.det (monomialMinor y (fun i => (e i).val)) else 0 := by
  rw [det_truncatedSeriesMatrix_minor, det_constantPowerMatrix_minor]
  have hmul (a b : R) (k : ℕ) :
      (PowerSeries.C a * PowerSeries.X ^ k) * PowerSeries.C b =
        PowerSeries.C (a * b) * PowerSeries.X ^ k := by
    rw [map_mul]
    ring
  rw [hmul, PowerSeries.coeff_C_mul_X_pow]

/-- The determinant coefficient is a finite sum of coefficient and monomial minors. -/
theorem coeff_det_seriesAlternantMatrix_eq_minor_sum {m : ℕ}
    (H : PowerSeries R) (y : Fin m → R) (L n : ℕ) (hn : n ≤ L) :
    PowerSeries.coeff n (Matrix.det (seriesAlternantMatrix H y)) =
      ∑ S : {S : Finset (Fin (L + 1)) // S.card = m},
        if n = ∑ i, (S.val.orderEmbOfFin S.property i).val then
          Matrix.det (seriesCoefficientMinor H
            (fun i => (S.val.orderEmbOfFin S.property i).val)) *
          Matrix.det (monomialMinor y (fun i => (S.val.orderEmbOfFin S.property i).val))
        else 0 := by
  rw [coeff_det_seriesAlternantMatrix H y L n hn]
  apply Finset.sum_congr rfl
  intro S _
  exact coeff_minor_product H y L n _

/-- Simultaneously reordering the two minor indices does not change their product. -/
theorem det_minor_product_permute {m : ℕ} (A B : Matrix (Fin m) (Fin m) R)
    (σ : Equiv.Perm (Fin m)) :
    Matrix.det (A.submatrix id σ) * Matrix.det (B.submatrix σ id) =
      Matrix.det A * Matrix.det B := by
  rw [← Matrix.det_mul, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.det_mul]

end Langlands.GeneralLinear.Spherical
