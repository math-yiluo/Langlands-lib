import Langlands.Representation.Conductor.SphericalSeries
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Finite denominator multiplication of the spherical Laurent series -/

noncomputable section

namespace Langlands.Conductor

open scoped BigOperators

universe uK uσ uA uB

section FiniteMultiplier

variable {A : Type uA} [CommRing A]

/-- A polynomial regarded as a Laurent series with nonnegative exponents. -/
def finitePolynomialLaurentSeries (P : Polynomial A) : LaurentSeries A :=
  ∑ m ∈ P.support, HahnSeries.single (m : ℤ) (P.coeff m)

@[simp] theorem finitePolynomialLaurentSeries_coeff_nat (P : Polynomial A) (m : ℕ) :
    (finitePolynomialLaurentSeries P).coeff (m : ℤ) = P.coeff m := by
  classical
  by_cases hm : P.coeff m = 0 <;>
    simp [finitePolynomialLaurentSeries, HahnSeries.coeff_single, hm]

@[simp] theorem finitePolynomialLaurentSeries_coeff_negSucc
    (P : Polynomial A) (m : ℕ) :
    (finitePolynomialLaurentSeries P).coeff (Int.negSucc m) = 0 := by
  classical
  simp [finitePolynomialLaurentSeries]

/-- Multiplication by the finite series is the usual finite convolution. -/
theorem mul_finitePolynomialLaurentSeries_coeff
    (S : LaurentSeries A) (P : Polynomial A) (d : ℤ) :
    (S * finitePolynomialLaurentSeries P).coeff d =
      ∑ m ∈ P.support, S.coeff (d - (m : ℤ)) * P.coeff m := by
  classical
  simp [finitePolynomialLaurentSeries, Finset.mul_sum, HahnSeries.coeff_mul_single]

/-- A multiplier with nonnegative exponents preserves every lower bound. -/
theorem mul_finitePolynomialLaurentSeries_coeff_eq_zero_below
    (S : LaurentSeries A) (P : Polynomial A) (d₀ : ℤ)
    (hS : ∀ d < d₀, S.coeff d = 0) :
    ∀ d < d₀, (S * finitePolynomialLaurentSeries P).coeff d = 0 := by
  intro d hd
  rw [mul_finitePolynomialLaurentSeries_coeff]
  apply Finset.sum_eq_zero
  intro m _
  rw [hS (d - (m : ℤ)) (by omega), zero_mul]

variable {B : Type uB} [CommRing B]

theorem finitePolynomialLaurentSeries_map
    (P : Polynomial A) (f : A →+* B) :
    (finitePolynomialLaurentSeries P).map f =
      finitePolynomialLaurentSeries (P.map f) := by
  ext d
  cases d <;> simp

theorem mul_finitePolynomialLaurentSeries_map
    (S : LaurentSeries A) (P : Polynomial A) (f : A →+* B) :
    (S * finitePolynomialLaurentSeries P).map f =
      S.map f * finitePolynomialLaurentSeries (P.map f) := by
  have hf := HahnSeries.map_mul f.toNonUnitalRingHom
    (x := S) (y := finitePolynomialLaurentSeries P)
  change (S * finitePolynomialLaurentSeries P).map f =
    S.map f * (finitePolynomialLaurentSeries P).map f at hf
  rw [finitePolynomialLaurentSeries_map] at hf
  exact hf

end FiniteMultiplier

section Homogeneity

variable {σ : Type uσ} {K : Type uK} [Fintype σ] [Field K]

theorem IsSymmetricTorusHomogeneous.mul
    {p r : symmetricTorusSubalgebra σ K} {a b : ℤ}
    (hp : IsSymmetricTorusHomogeneous σ K p a)
    (hr : IsSymmetricTorusHomogeneous σ K r b) :
    IsSymmetricTorusHomogeneous σ K (p * r) (a + b) := by
  intro c
  simp only [map_mul, hp c, hr c, zpow_add₀ c.ne_zero]
  ring

/-- The finite convolution preserves equality of Laurent and torus degree. -/
theorem mul_finitePolynomialLaurentSeries_coeff_isHomogeneous
    (S : LaurentSeries (symmetricTorusSubalgebra σ K))
    (P : Polynomial (symmetricTorusSubalgebra σ K))
    (hS : ∀ d, IsSymmetricTorusHomogeneous σ K (S.coeff d) d)
    (hP : ∀ m, IsSymmetricTorusHomogeneous σ K (P.coeff m) (m : ℤ))
    (d : ℤ) :
    IsSymmetricTorusHomogeneous σ K
      ((S * finitePolynomialLaurentSeries P).coeff d) d := by
  rw [mul_finitePolynomialLaurentSeries_coeff]
  apply (symmetricTorusHomogeneousSubmodule σ K d).sum_mem
  intro m _
  change IsSymmetricTorusHomogeneous σ K
    (S.coeff (d - (m : ℤ)) * P.coeff m) d
  have hm := (hS (d - (m : ℤ))).mul (hP m)
  simpa only [sub_add_cancel] using hm

end Homogeneity

section DenominatorPolynomial

open MvPolynomial

variable (σ : Type uσ) (K : Type uK) [Fintype σ] [Field K]

/-- The actual coordinate product of a scalar polynomial. -/
def coordinatePolynomialProduct (P : Polynomial K) : MvPolynomial σ K :=
  ∏ i : σ, Polynomial.aeval (X i) P

theorem coordinatePolynomialProduct_isSymmetric (P : Polynomial K) :
    (coordinatePolynomialProduct σ K P).IsSymmetric := by
  intro e
  simp only [coordinatePolynomialProduct, map_prod]
  have he (i : σ) :
      rename e (Polynomial.aeval (X i : MvPolynomial σ K) P) =
        Polynomial.aeval (X (e i) : MvPolynomial σ K) P := by
    rw [← AlgHom.comp_apply, ← Polynomial.aeval_algHom]
    simp
  simp only [he]
  exact Equiv.prod_comp e (fun i : σ =>
    Polynomial.aeval (X i : MvPolynomial σ K) P)

theorem homogeneousComponent_coordinatePolynomialProduct_isSymmetric
    (P : Polynomial K) (m : ℕ) :
    (homogeneousComponent m (coordinatePolynomialProduct σ K P)).IsSymmetric := by
  intro e
  rw [rename_homogeneousComponent,
    coordinatePolynomialProduct_isSymmetric σ K P e]

/-- Embed an actual symmetric polynomial into the symmetric Laurent algebra. -/
def symmetricPolynomialToTorus :
    symmetricSubalgebra σ K →ₐ[K] symmetricTorusSubalgebra σ K where
  toFun p := ⟨algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) p.val,
    fun e => by
      rw [torusPolynomialPermutation_algebraMap, p.property e]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' p r := Subtype.ext (map_mul _ p.val r.val)
  map_zero' := Subtype.ext (map_zero _)
  map_add' p r := Subtype.ext (map_add _ p.val r.val)
  commutes' a := Subtype.ext (IsScalarTower.algebraMap_apply K
    (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) a).symm

@[simp] theorem symmetricTorusEvaluation_symmetricPolynomialToTorus
    (p : symmetricSubalgebra σ K) (x : σ → Kˣ) :
    symmetricTorusEvaluation σ K x (symmetricPolynomialToTorus σ K p) =
      eval (fun i => (x i : K)) p.val := by
  change torusPolynomialEvaluation σ K x
    (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) p.val) = _
  rw [torusPolynomialEvaluation_algebraMap]
  rfl

omit [Fintype σ] in
/-- The standard scaling identity, proved monomial by monomial. -/
theorem homogeneousPolynomial_eval_scale
    (p : MvPolynomial σ K) {m : ℕ} (hp : p.IsHomogeneous m)
    (c : K) (x : σ → K) :
    eval (fun i => c * x i) p = c ^ m * eval x p := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hp.degree_eq_sum_deg_support ha]
  ring

theorem symmetricPolynomialToTorus_isHomogeneous [Infinite K]
    (p : symmetricSubalgebra σ K) {m : ℕ} (hp : p.val.IsHomogeneous m) :
    IsSymmetricTorusHomogeneous σ K
      (symmetricPolynomialToTorus σ K p) (m : ℤ) := by
  intro c
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [symmetricTorusEvaluation_scale, map_mul, AlgHom.commutes,
    symmetricTorusEvaluation_symmetricPolynomialToTorus,
    symmetricTorusEvaluation_symmetricPolynomialToTorus]
  simpa only [Units.val_mul, zpow_natCast, Algebra.algebraMap_self,
    RingHom.id_apply] using
    homogeneousPolynomial_eval_scale σ K p.val hp (c : K) (fun i => (x i : K))

/-- The homogeneous degree `m` coefficient of the actual coordinate product. -/
def coordinateDenominatorCoefficient (P : Polynomial K) (m : ℕ) :
    symmetricTorusSubalgebra σ K :=
  symmetricPolynomialToTorus σ K
    ⟨homogeneousComponent m (coordinatePolynomialProduct σ K P),
      homogeneousComponent_coordinatePolynomialProduct_isSymmetric σ K P m⟩

@[simp] theorem symmetricTorusEvaluation_coordinateDenominatorCoefficient
    (P : Polynomial K) (m : ℕ) (x : σ → Kˣ) :
    symmetricTorusEvaluation σ K x (coordinateDenominatorCoefficient σ K P m) =
      eval (fun i => (x i : K))
        (homogeneousComponent m (coordinatePolynomialProduct σ K P)) :=
  symmetricTorusEvaluation_symmetricPolynomialToTorus σ K _ x

theorem coordinateDenominatorCoefficient_isHomogeneous [Infinite K]
    (P : Polynomial K) (m : ℕ) :
    IsSymmetricTorusHomogeneous σ K
      (coordinateDenominatorCoefficient σ K P m) (m : ℤ) :=
  symmetricPolynomialToTorus_isHomogeneous σ K _
    (homogeneousComponent_isHomogeneous m _)

theorem coordinateDenominatorCoefficient_eq_zero
    (P : Polynomial K) (m : ℕ)
    (hm : (coordinatePolynomialProduct σ K P).totalDegree < m) :
    coordinateDenominatorCoefficient σ K P m = 0 := by
  apply Subtype.ext
  change algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K)
    (homogeneousComponent m (coordinatePolynomialProduct σ K P)) = 0
  rw [homogeneousComponent_eq_zero m _ hm, map_zero]

/-- The finite polynomial whose specialization is `∏ i, P(X * xᵢ)`. -/
def coordinateDenominatorPolynomial (P : Polynomial K) :
    Polynomial (symmetricTorusSubalgebra σ K) :=
  ∑ m ∈ Finset.range ((coordinatePolynomialProduct σ K P).totalDegree + 1),
    Polynomial.monomial m (coordinateDenominatorCoefficient σ K P m)

@[simp] theorem coordinateDenominatorPolynomial_coeff (P : Polynomial K) (m : ℕ) :
    (coordinateDenominatorPolynomial σ K P).coeff m =
      coordinateDenominatorCoefficient σ K P m := by
  classical
  by_cases hm : m ∈ Finset.range ((coordinatePolynomialProduct σ K P).totalDegree + 1)
  · simp [coordinateDenominatorPolynomial, Polynomial.coeff_monomial, hm]
  · have hz := coordinateDenominatorCoefficient_eq_zero σ K P m (by
      simp only [Finset.mem_range, not_lt] at hm
      omega)
    simp [coordinateDenominatorPolynomial, Polynomial.coeff_monomial, hm, hz]

theorem coordinateDenominatorPolynomial_coeff_isHomogeneous [Infinite K]
    (P : Polynomial K) (m : ℕ) :
    IsSymmetricTorusHomogeneous σ K
      ((coordinateDenominatorPolynomial σ K P).coeff m) (m : ℤ) := by
  rw [coordinateDenominatorPolynomial_coeff]
  exact coordinateDenominatorCoefficient_isHomogeneous σ K P m

theorem coordinateDenominatorPolynomial_eval₂ (P : Polynomial K)
    (x : σ → Kˣ) (t : K) :
    (coordinateDenominatorPolynomial σ K P).eval₂
      (symmetricTorusEvaluation σ K x).toRingHom t =
      ∏ i : σ, P.eval (t * (x i : K)) := by
  classical
  simp only [coordinateDenominatorPolynomial, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_monomial]
  change (∑ m ∈ Finset.range ((coordinatePolynomialProduct σ K P).totalDegree + 1),
    symmetricTorusEvaluation σ K x (coordinateDenominatorCoefficient σ K P m) *
      t ^ m) = _
  simp only [symmetricTorusEvaluation_coordinateDenominatorCoefficient]
  have he :
      (∑ m ∈ Finset.range ((coordinatePolynomialProduct σ K P).totalDegree + 1),
        eval (fun i => (x i : K))
          (homogeneousComponent m (coordinatePolynomialProduct σ K P)) * t ^ m) =
      eval (fun i => t * (x i : K)) (coordinatePolynomialProduct σ K P) := by
    calc
      _ = ∑ m ∈ Finset.range ((coordinatePolynomialProduct σ K P).totalDegree + 1),
          eval (fun i => t * (x i : K))
            (homogeneousComponent m (coordinatePolynomialProduct σ K P)) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [homogeneousPolynomial_eval_scale σ K _
          (homogeneousComponent_isHomogeneous m _) t]
        ring
      _ = _ := by rw [← map_sum, sum_homogeneousComponent]
  rw [he]
  simp only [coordinatePolynomialProduct, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  change (MvPolynomial.aeval (fun j => t * (x j : K)))
    (Polynomial.aeval (X i : MvPolynomial σ K) P) = _
  rw [← AlgHom.comp_apply, ← Polynomial.aeval_algHom]
  simp only [MvPolynomial.aeval_X, Polynomial.coe_aeval_eq_eval]

theorem coordinateDenominatorPolynomial_specialize [Infinite K]
    (P : Polynomial K) (x : σ → Kˣ) :
    (coordinateDenominatorPolynomial σ K P).map
      (symmetricTorusEvaluation σ K x).toRingHom =
      ∏ i : σ, P.comp (Polynomial.C (x i : K) * Polynomial.X) := by
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_map, coordinateDenominatorPolynomial_eval₂]
  simp only [Polynomial.eval_prod, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, mul_comm t]

end DenominatorPolynomial

end Langlands.Conductor
