import Langlands.Representation.RankinSelberg.FiniteCauchyBinet
import Mathlib.RingTheory.PowerSeries.Trunc

/-! # Finite minor expansions of power series alternants -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

variable {R : Type*} [CommRing R]

/-- A power series coefficient extended by zero to negative integer degrees. -/
def seriesCoeff (H : PowerSeries R) (k : ℤ) : R :=
  if 0 ≤ k then PowerSeries.coeff k.toNat H else 0

/-- Equality through degree `n` is preserved by finite products. -/
theorem coeff_prod_congr {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (A B : ι → PowerSeries R) (n : ℕ)
    (h : ∀ i ∈ s, ∀ k ≤ n, PowerSeries.coeff k (A i) = PowerSeries.coeff k (B i)) :
    PowerSeries.coeff n (∏ i ∈ s, A i) = PowerSeries.coeff n (∏ i ∈ s, B i) := by
  rw [PowerSeries.coeff_prod, PowerSeries.coeff_prod]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.prod_congr rfl
  intro i hi
  apply h i hi
  have hsum := (Finset.mem_finsuppAntidiag.mp hf).1
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) hi).trans hsum.le

/-- A determinant coefficient only depends on entry coefficients up to that degree. -/
theorem coeff_det_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι (PowerSeries R)) (n : ℕ)
    (h : ∀ i j k, k ≤ n → PowerSeries.coeff k (A i j) = PowerSeries.coeff k (B i j)) :
    PowerSeries.coeff n (Matrix.det A) = PowerSeries.coeff n (Matrix.det B) := by
  rw [Matrix.det_apply', Matrix.det_apply', map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have hsign : (((Equiv.Perm.sign σ : ℤ) : PowerSeries R)) =
      PowerSeries.C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
  rw [hsign, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  congr 1
  exact coeff_prod_congr Finset.univ _ _ n (fun i _ k hk => h (σ i) i k hk)

/-- The base alternant with reversed exponents. -/
def reverseVandermonde {m : ℕ} (y : Fin m → R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i j => y j ^ i.rev.val

/-- Multiply every alternant column by the generating series at that variable. -/
def seriesAlternantMatrix {m : ℕ} (H : PowerSeries R) (y : Fin m → R) :
    Matrix (Fin m) (Fin m) (PowerSeries R) :=
  Matrix.of fun i j => (PowerSeries.C (y j) * PowerSeries.X) ^ i.rev.val *
    PowerSeries.rescale (y j) H

/-- The finite coefficient matrix used to truncate the row generating functions. -/
def truncatedSeriesMatrix {m : ℕ} (H : PowerSeries R) (L : ℕ) :
    Matrix (Fin m) (Fin (L + 1)) (PowerSeries R) :=
  Matrix.of fun i l => PowerSeries.monomial l.val (seriesCoeff H ((l.val : ℤ) - i.rev.val))

/-- Constant powers of the second alphabet. -/
def constantPowerMatrix {m : ℕ} (y : Fin m → R) (L : ℕ) :
    Matrix (Fin (L + 1)) (Fin m) (PowerSeries R) :=
  Matrix.of fun l j => PowerSeries.C (y j ^ l.val)

/-- Column factorization of the generating-series determinant. -/
theorem det_seriesAlternantMatrix {m : ℕ} (H : PowerSeries R) (y : Fin m → R) :
    Matrix.det (seriesAlternantMatrix H y) =
      PowerSeries.X ^ (∑ i : Fin m, i.rev.val) *
        PowerSeries.C (Matrix.det (reverseVandermonde y)) *
          ∏ j : Fin m, PowerSeries.rescale (y j) H := by
  have hmat : seriesAlternantMatrix H y =
      Matrix.diagonal (fun i : Fin m => (PowerSeries.X : PowerSeries R) ^ i.rev.val) *
        (reverseVandermonde y).map PowerSeries.C *
          Matrix.diagonal (fun j => PowerSeries.rescale (y j) H) := by
    apply Matrix.ext
    intro i j
    simp [seriesAlternantMatrix, reverseVandermonde, Matrix.diagonal_mul,
      Matrix.mul_diagonal, mul_pow, map_pow]
    ring
  have hd : Matrix.det ((reverseVandermonde y).map PowerSeries.C) =
      PowerSeries.C (Matrix.det (reverseVandermonde y)) :=
    ((PowerSeries.C : R →+* PowerSeries R).map_det (reverseVandermonde y)).symm
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    hd, Finset.prod_pow_eq_pow_sum]

/-- The entry coefficients before the truncation limit are unchanged. -/
theorem coeff_truncatedSeries_mul {m : ℕ} (H : PowerSeries R) (y : Fin m → R)
    (L k : ℕ) (hk : k ≤ L) (i j : Fin m) :
    PowerSeries.coeff k ((truncatedSeriesMatrix H L * constantPowerMatrix y L) i j) =
      seriesCoeff H ((k : ℤ) - i.rev.val) * y j ^ k := by
  change PowerSeries.coeff k
    (∑ l : Fin (L + 1), PowerSeries.monomial l.val
      (seriesCoeff H ((l.val : ℤ) - i.rev.val)) * PowerSeries.C (y j ^ l.val)) = _
  rw [map_sum]
  simp_rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_monomial]
  rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin (L + 1))]
  · simp
  · intro l _ hl
    have hkl : k ≠ l.val := fun h => hl (Fin.ext h.symm)
    simp [hkl]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Coefficients of a rescaled row generating function. -/
theorem coeff_seriesAlternantMatrix {m : ℕ} (H : PowerSeries R) (y : Fin m → R)
    (k : ℕ) (i j : Fin m) :
    PowerSeries.coeff k (seriesAlternantMatrix H y i j) =
      seriesCoeff H ((k : ℤ) - i.rev.val) * y j ^ k := by
  change PowerSeries.coeff k
    ((PowerSeries.C (y j) * PowerSeries.X) ^ i.rev.val * PowerSeries.rescale (y j) H) = _
  rw [mul_pow, ← map_pow, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul']
  by_cases hi : i.rev.val ≤ k
  · rw [ite_eq_left hi, PowerSeries.coeff_rescale, seriesCoeff, ite_eq_left (by omega)]
    have he : ((k : ℤ) - i.rev.val).toNat = k - i.rev.val := by omega
    rw [he]
    have hp : y j ^ i.rev.val * y j ^ (k - i.rev.val) = y j ^ k := by
      rw [← pow_add, Nat.add_sub_of_le hi]
    calc
      _ = (PowerSeries.coeff (k - i.rev.val) H) *
          (y j ^ i.rev.val * y j ^ (k - i.rev.val)) := by ring
      _ = _ := by rw [hp]
  · rw [ite_eq_right hi, mul_zero, seriesCoeff, ite_eq_right (by omega), zero_mul]

/-- Cauchy–Binet may be applied after any sufficiently long finite truncation. -/
theorem coeff_det_seriesAlternantMatrix {m : ℕ} (H : PowerSeries R) (y : Fin m → R)
    (L n : ℕ) (hn : n ≤ L) :
    PowerSeries.coeff n (Matrix.det (seriesAlternantMatrix H y)) =
      ∑ S : {S : Finset (Fin (L + 1)) // S.card = m},
        PowerSeries.coeff n
          (Matrix.det ((truncatedSeriesMatrix H L).submatrix id (S.val.orderEmbOfFin S.property)) *
            Matrix.det ((constantPowerMatrix y L).submatrix (S.val.orderEmbOfFin S.property) id)) := by
  rw [coeff_det_congr (seriesAlternantMatrix H y)
    (truncatedSeriesMatrix H L * constantPowerMatrix y L) n
    (fun i j k hk => (coeff_seriesAlternantMatrix H y k i j).trans
      (coeff_truncatedSeries_mul H y L k (hk.trans hn) i j).symm)]
  rw [det_rectangular_mul, map_sum]

end Langlands.GeneralLinear.Spherical
