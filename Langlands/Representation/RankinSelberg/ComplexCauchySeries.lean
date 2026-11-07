import Langlands.Representation.RankinSelberg.CompleteCauchySeries

/-! # Specialization of the two-alphabet Cauchy series to complex parameters -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

open MvPolynomial

variable {σ R S : Type*} [Fintype σ] [DecidableEq σ] [CommRing R] [CommRing S]

theorem map_completeSymm (f : R →+* S) (k : ℤ) :
    MvPolynomial.map f (completeSymm σ R k) = completeSymm σ S k := by
  by_cases hk : 0 ≤ k <;> simp [completeSymm, hk, MvPolynomial.map_hsymm]

theorem map_jacobiTrudiIn (f : R →+* S) {m : ℕ} (α : Fin m → ℤ) :
    MvPolynomial.map f (jacobiTrudiIn σ R α) = jacobiTrudiIn σ S α := by
  have hmat :
      (Matrix.of fun i j : Fin m => completeSymm σ R (α i - i + j)).map (MvPolynomial.map f) =
        Matrix.of (fun i j : Fin m => completeSymm σ S (α i - i + j)) := by
    apply Matrix.ext
    intro i j
    exact map_completeSymm f _
  exact ((MvPolynomial.map f).map_det _).trans (congrArg Matrix.det hmat)

theorem eval₂Hom_jacobiTrudiIn (f : R →+* S) (y : σ → S) {m : ℕ} (α : Fin m → ℤ) :
    MvPolynomial.eval₂Hom f y (jacobiTrudiIn σ R α) =
      MvPolynomial.eval y (jacobiTrudiIn σ S α) := by
  change MvPolynomial.eval₂ f y (jacobiTrudiIn σ R α) = _
  rw [MvPolynomial.eval₂_eq_eval_map, map_jacobiTrudiIn]

/-- Evaluate the two independent polynomial alphabets at supplied complex parameters. -/
def complexCauchyEval {n : ℕ} (x : σ → ℂ) (y : Fin (n + 1) → ℂ) :
    MvPolynomial (Fin (n + 1)) (MvPolynomial σ ℂ) →+* ℂ :=
  MvPolynomial.eval₂Hom (MvPolynomial.eval x) y

/-- The formal Cauchy series at arbitrary, possibly repeated or zero complex parameters. -/
def complexCauchySeries {n : ℕ} (x : σ → ℂ) (y : Fin (n + 1) → ℂ) : PowerSeries ℂ :=
  PowerSeries.map (complexCauchyEval x y) (completeCauchySeries σ ℂ n)

/-- The degree coefficient is the actual evaluated two-alphabet Jacobi–Trudi sum. -/
theorem coeff_complexCauchySeries {n : ℕ} (x : σ → ℂ) (y : Fin (n + 1) → ℂ) (d : ℕ) :
    PowerSeries.coeff d (complexCauchySeries x y) =
      ∑ α : DegreePartition n d,
        MvPolynomial.eval x (jacobiTrudiIn σ ℂ (degreePartitionWeight α)) *
          MvPolynomial.eval y (jacobiTrudi ℂ (degreePartitionWeight α)) := by
  rw [complexCauchySeries, PowerSeries.coeff_map, coeff_completeCauchySeries, map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [map_mul]
  change MvPolynomial.eval₂Hom (MvPolynomial.eval x) y
      (MvPolynomial.C (jacobiTrudiIn σ ℂ (degreePartitionWeight α))) *
    MvPolynomial.eval₂Hom (MvPolynomial.eval x) y
      (jacobiTrudiIn (Fin (n + 1)) (MvPolynomial σ ℂ) (degreePartitionWeight α)) = _
  rw [MvPolynomial.eval₂Hom_C, eval₂Hom_jacobiTrudiIn]
  rfl

/-- The specialized series retains the exact inverse pair-product identity. -/
theorem complexCauchySeries_mul_pairProduct {n : ℕ} (x : σ → ℂ) (y : Fin (n + 1) → ℂ) :
    complexCauchySeries x y *
      (∏ j : Fin (n + 1), ∏ i : σ,
        (1 - PowerSeries.C (x i * y j) * PowerSeries.X)) = 1 := by
  have h := congrArg (PowerSeries.map (complexCauchyEval x y))
    (completeCauchySeries_mul_pairProduct σ ℂ n)
  simpa only [map_mul, map_prod, map_sub, map_one, PowerSeries.map_C, PowerSeries.map_X,
    complexCauchyEval, complexCauchySeries, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X]
    using h

/-- Complete symmetric coefficients at the first alphabet are a finite product of geometric series. -/
theorem map_eval_completeSeries (x : σ → ℂ) :
    PowerSeries.map (MvPolynomial.eval x) (completeSeries σ ℂ) =
      ∏ i : σ, PowerSeries.mk (fun k : ℕ => x i ^ k) := by
  rw [completeSeries_eq_prod, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  apply PowerSeries.ext
  intro k
  simp [PowerSeries.coeff_map]

/-- The specialized construction is a product of rescaled first-alphabet series. -/
theorem complexCauchySeries_eq_rescaled {n : ℕ} (x : σ → ℂ) (y : Fin (n + 1) → ℂ) :
    complexCauchySeries x y =
      ∏ j : Fin (n + 1), PowerSeries.rescale (y j)
        (PowerSeries.map (MvPolynomial.eval x) (completeSeries σ ℂ)) := by
  unfold complexCauchySeries completeCauchySeries
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [← PowerSeries.rescale_map]
  have hmap :
      PowerSeries.map (complexCauchyEval x y)
        (PowerSeries.map (MvPolynomial.C : MvPolynomial σ ℂ →+*
          MvPolynomial (Fin (n + 1)) (MvPolynomial σ ℂ)) (completeSeries σ ℂ)) =
        PowerSeries.map (MvPolynomial.eval x) (completeSeries σ ℂ) := by
    apply PowerSeries.ext
    intro k
    simp [complexCauchyEval]
  rw [hmap]
  simp [complexCauchyEval]

/-- The specialized Cauchy series is the finite product of all pair geometric series. -/
theorem complexCauchySeries_eq_geometric {n : ℕ} (x : σ → ℂ) (y : Fin (n + 1) → ℂ) :
    complexCauchySeries x y =
      ∏ j : Fin (n + 1), ∏ i : σ, PowerSeries.mk (fun k : ℕ => (x i * y j) ^ k) := by
  rw [complexCauchySeries_eq_rescaled, map_eval_completeSeries]
  apply Finset.prod_congr rfl
  intro j _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [PowerSeries.rescale_mk]
  congr 1
  funext k
  rw [mul_pow, mul_comm]

end Langlands.GeneralLinear.Spherical
