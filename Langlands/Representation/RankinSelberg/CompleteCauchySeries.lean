import Langlands.Representation.RankinSelberg.FormalCauchyIdentity
import Langlands.Representation.RankinSelberg.SymmetricGeneratingSeries

/-! # The two-alphabet complete symmetric Cauchy series -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

open MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

theorem seriesCoeff_map (f : R →+* S) (H : PowerSeries R) (k : ℤ) :
    seriesCoeff (PowerSeries.map f H) k = f (seriesCoeff H k) := by
  by_cases hk : 0 ≤ k <;> simp [seriesCoeff, hk]

theorem seriesJacobiTrudi_map (f : R →+* S) (H : PowerSeries R) {m : ℕ}
    (α : Fin m → ℤ) :
    seriesJacobiTrudi (PowerSeries.map f H) α = f (seriesJacobiTrudi H α) := by
  have hmat :
      Matrix.of (fun i j : Fin m => seriesCoeff (PowerSeries.map f H) (α i - i + j)) =
        (Matrix.of fun i j : Fin m => seriesCoeff H (α i - i + j)).map f := by
    apply Matrix.ext
    intro i j
    exact seriesCoeff_map f H _
  unfold seriesJacobiTrudi
  rw [hmat]
  exact (f.map_det _).symm

variable (σ R : Type*) [Fintype σ] [DecidableEq σ] [CommRing R]

/-- Jacobi–Trudi of any matrix rank in a supplied finite alphabet. -/
def jacobiTrudiIn {m : ℕ} (α : Fin m → ℤ) : MvPolynomial σ R :=
  Matrix.det (Matrix.of fun i j : Fin m => completeSymm σ R (α i - i + j))

theorem seriesJacobiTrudi_completeSeries {m : ℕ} (α : Fin m → ℤ) :
    seriesJacobiTrudi (completeSeries σ R) α = jacobiTrudiIn σ R α := by
  unfold seriesJacobiTrudi jacobiTrudiIn
  congr 1
  apply Matrix.ext
  intro i j
  simp [seriesCoeff, completeSymm, completeSeries]

/-- The first alphabet's complete generating series rescaled at each second variable. -/
def completeCauchySeries (n : ℕ) :
    PowerSeries (MvPolynomial (Fin (n + 1)) (MvPolynomial σ R)) :=
  ∏ j : Fin (n + 1), PowerSeries.rescale (X j)
    (PowerSeries.map (MvPolynomial.C : MvPolynomial σ R →+*
      MvPolynomial (Fin (n + 1)) (MvPolynomial σ R)) (completeSeries σ R))

/-- The exact two-alphabet Schur coefficient sum, with arbitrary alphabet sizes. -/
theorem coeff_completeCauchySeries [IsDomain R] (n d : ℕ) :
    PowerSeries.coeff d (completeCauchySeries σ R n) =
      ∑ α : DegreePartition n d,
        MvPolynomial.C (jacobiTrudiIn σ R (degreePartitionWeight α)) *
          jacobiTrudi (MvPolynomial σ R) (degreePartitionWeight α) := by
  have h := formal_cauchy_coeff (MvPolynomial σ R)
    (PowerSeries.map (MvPolynomial.C : MvPolynomial σ R →+*
      MvPolynomial (Fin (n + 1)) (MvPolynomial σ R)) (completeSeries σ R)) d
  simpa only [completeCauchySeries, seriesJacobiTrudi_map,
    seriesJacobiTrudi_completeSeries] using h

omit [Fintype σ] [DecidableEq σ] in
private theorem rescale_constant (a b : R) :
    PowerSeries.rescale a (PowerSeries.C b) = PowerSeries.C b := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

/-- The formal Cauchy series is the inverse of the product of all pair factors. -/
theorem completeCauchySeries_mul_pairProduct (n : ℕ) :
    completeCauchySeries σ R n *
      (∏ j : Fin (n + 1), ∏ i : σ,
        (1 - PowerSeries.C
          ((MvPolynomial.C (X i : MvPolynomial σ R)) * (X j : MvPolynomial (Fin (n + 1)) (MvPolynomial σ R))) *
            PowerSeries.X)) = 1 := by
  let f : MvPolynomial σ R →+* MvPolynomial (Fin (n + 1)) (MvPolynomial σ R) := MvPolynomial.C
  have hj (j : Fin (n + 1)) :
      PowerSeries.rescale (X j) (PowerSeries.map f (completeSeries σ R)) *
        (∏ i : σ, (1 - PowerSeries.C (f (X i) * X j) * PowerSeries.X)) = 1 := by
    have h := congrArg (fun H => PowerSeries.rescale (X j) (PowerSeries.map f H))
      (completeSeries_mul_elementaryProduct σ R)
    simpa only [map_mul, map_prod, map_sub, map_one, PowerSeries.map_C,
      PowerSeries.map_X, rescale_constant, PowerSeries.rescale_X, mul_assoc] using h
  change (∏ j : Fin (n + 1), PowerSeries.rescale (X j) (PowerSeries.map f (completeSeries σ R))) *
    (∏ j : Fin (n + 1), ∏ i : σ, (1 - PowerSeries.C (f (X i) * X j) * PowerSeries.X)) = 1
  rw [← Finset.prod_mul_distrib]
  simp_rw [hj]
  exact Finset.prod_const_one

end Langlands.GeneralLinear.Spherical
