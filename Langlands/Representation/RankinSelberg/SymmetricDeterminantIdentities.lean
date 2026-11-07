import Langlands.Representation.RankinSelberg.SymmetricGeneratingSeries

/-! # Finite coefficient and determinant identities for symmetric functions -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

omit [Fintype σ] [DecidableEq σ] in
/-- The coefficient of a finite product of linear series is the subset sum. -/
theorem coeff_prod_linear (x : σ → R) (s : Finset σ) (n : ℕ) :
    PowerSeries.coeff n (∏ i ∈ s,
      (1 + PowerSeries.C (x i) * PowerSeries.X)) =
      ∑ t ∈ s.powersetCard n, ∏ i ∈ t, x i := by
  rw [Finset.prod_one_add, map_sum]
  simp_rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const,
    PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  simp only [eq_comm]

/-- Choose rows from `B` on `s` and from `A` elsewhere. -/
def selectRows (A B : Matrix σ σ R) (s : Finset σ) : Matrix σ σ R :=
  Matrix.of fun i j => if i ∈ s then B i j else A i j

/-- Expand a determinant by choosing the second summand in a subset of rows. -/
theorem det_add_scalar (A B : Matrix σ σ R) (t : R) :
    Matrix.det (Matrix.of fun i j => A i j + t * B i j) =
      ∑ s : Finset σ, t ^ s.card * Matrix.det (selectRows A B s) := by
  have hmat : Matrix.of (fun i j => A i j + t * B i j) =
      t • B + A := by
    ext i j
    simp [add_comm]
  rw [hmat]
  change Matrix.detRowAlternating ((fun i => t • B i) + (fun i => A i)) = _
  rw [AlternatingMap.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  have hrows : s.piecewise (fun i => t • B i) A =
      fun i => (if i ∈ s then t else 1) • selectRows A B s i := by
    funext i j
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, selectRows, hi]
  erw [hrows, AlternatingMap.map_smul_univ]
  simp [Matrix.det, smul_eq_mul]

omit [DecidableEq σ] in
/-- The elementary symmetric polynomial is the coefficient of its linear product. -/
theorem coeff_elementaryProduct (n : ℕ) :
    PowerSeries.coeff n
      (∏ i : σ, (1 + PowerSeries.C (MvPolynomial.X i : MvPolynomial σ R) *
        PowerSeries.X)) = MvPolynomial.esymm σ R n := by
  exact coeff_prod_linear _ Finset.univ n

/-- Coefficients select the terms with precisely `k` rows from the second matrix. -/
theorem coeff_det_add_series (A B : Matrix σ σ R) (k : ℕ) :
    PowerSeries.coeff k
      (Matrix.det (Matrix.of fun i j => PowerSeries.C (A i j) +
        PowerSeries.X * PowerSeries.C (B i j))) =
      ∑ s ∈ (Finset.univ : Finset σ).powersetCard k,
        Matrix.det (selectRows A B s) := by
  erw [det_add_scalar (A.map PowerSeries.C) (B.map PowerSeries.C) PowerSeries.X,
    map_sum]
  have hmap (s : Finset σ) :
      selectRows (A.map PowerSeries.C) (B.map PowerSeries.C) s =
        (selectRows A B s).map PowerSeries.C := by
    apply Matrix.ext
    intro i j
    by_cases hi : i ∈ s <;> simp [selectRows, hi]
  have hdet (s : Finset σ) :
      Matrix.det (selectRows (A.map PowerSeries.C) (B.map PowerSeries.C) s) =
        PowerSeries.C (Matrix.det (selectRows A B s)) := by
    rw [hmap]
    exact ((PowerSeries.C : R →+* PowerSeries R).map_det (selectRows A B s)).symm
  simp_rw [hdet, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
  simp [Finset.powersetCard_eq_filter, Finset.sum_filter, eq_comm]

/-- Column multiplication turns the subset determinant sum into an elementary sum. -/
theorem sum_det_column_scaled (A : Matrix σ σ R) (x : σ → R) (k : ℕ) :
    (∑ s ∈ (Finset.univ : Finset σ).powersetCard k,
      Matrix.det (selectRows A (Matrix.of fun i j => A i j * x j) s)) =
        Matrix.det A * (∑ s ∈ (Finset.univ : Finset σ).powersetCard k,
          ∏ i ∈ s, x i) := by
  erw [← coeff_det_add_series A (Matrix.of fun i j => A i j * x j) k]
  have hmat :
      Matrix.of (fun i j => PowerSeries.C (A i j) +
        PowerSeries.X * PowerSeries.C (A i j * x j)) =
      A.map PowerSeries.C * Matrix.diagonal
        (fun j => 1 + PowerSeries.C (x j) * PowerSeries.X) := by
    apply Matrix.ext
    intro i j
    simp [map_mul, Matrix.mul_diagonal]
    ring
  simp only [Matrix.of_apply]
  erw [hmat, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.map_det,
    PowerSeries.coeff_C_mul, coeff_prod_linear]

end Langlands.GeneralLinear.Spherical
