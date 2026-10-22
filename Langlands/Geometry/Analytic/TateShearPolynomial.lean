import Langlands.Geometry.Analytic.TateRegrouping
import Langlands.Geometry.Analytic.TateCoordinateChange
import Langlands.Geometry.Analytic.SeparatingWeights
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Monic

/-! # Polynomial images of monomials under actual analytic coordinate changes -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTateAlgebra

open scoped BigOperators

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem regroup_X_zero (n : ℕ) :
    regroupEquiv (A := K) n (X (Fin (n + 1)) K 0) =
      RestrictedSeries.ofPolynomial (StrictTateAlgebra (Fin n) K) Polynomial.X := by
  apply iteratedToFormal_injective n
  change iteratedToFormal n (regroup (X (Fin (n + 1)) K 0)) = _
  rw [iteratedToFormal_regroup]
  change MvPowerSeries.finSuccEquiv K n (MvPowerSeries.X 0) =
    PowerSeries.map (restrictedSubalgebra (Fin n) K).val.toRingHom
      (Polynomial.X : Polynomial (StrictTateAlgebra (Fin n) K)).toPowerSeries
  rw [MvPowerSeries.finSuccEquiv_X_zero, Polynomial.coe_X]
  exact (PowerSeries.map_X (restrictedSubalgebra (Fin n) K).val.toRingHom).symm

theorem regroup_X_succ (n : ℕ) (i : Fin n) :
    regroupEquiv (A := K) n (X (Fin (n + 1)) K i.succ) =
      algebraMap (StrictTateAlgebra (Fin n) K)
        (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K)) (X (Fin n) K i) := by
  apply iteratedToFormal_injective n
  change iteratedToFormal n (regroup (X (Fin (n + 1)) K i.succ)) = _
  rw [iteratedToFormal_regroup]
  change MvPowerSeries.finSuccEquiv K n (MvPowerSeries.X i.succ) =
    PowerSeries.map (restrictedSubalgebra (Fin n) K).val.toRingHom
      (PowerSeries.C (X (Fin n) K i))
  rw [MvPowerSeries.finSuccEquiv_X_succ]
  exact (PowerSeries.map_C (restrictedSubalgebra (Fin n) K).val.toRingHom
    (X (Fin n) K i)).symm

/-- The actual polynomial image of one coordinate after power substitution
and regrouping. Coordinate zero is the new polynomial variable. -/
def shearPolynomial (n b : ℕ) (i : Fin (n + 1)) :
    Polynomial (StrictTateAlgebra (Fin n) K) :=
  Fin.cases Polynomial.X
    (fun j : Fin n => Polynomial.X ^ (b ^ ((j : ℕ) + 1)) +
      Polynomial.C (X (Fin n) K j)) i

theorem shearPolynomial_monic (n : ℕ) {b : ℕ} (hb : 0 < b) (i : Fin (n + 1)) :
    (shearPolynomial (K := K) n b i).Monic := by
  refine Fin.cases Polynomial.monic_X (fun j => ?_) i
  exact Polynomial.monic_X_pow_add_C _ (pow_pos hb _).ne'

theorem shearPolynomial_natDegree (n b : ℕ) (i : Fin (n + 1)) :
    (shearPolynomial (K := K) n b i).natDegree = b ^ (i : ℕ) := by
  refine Fin.cases (by simp [shearPolynomial]) (fun j => ?_) i
  exact Polynomial.natDegree_X_pow_add_C

/-- The actual product polynomial assigned to a monomial exponent. -/
def shearMonomialPolynomial (n b : ℕ) (d : Fin (n + 1) →₀ ℕ) :
    Polynomial (StrictTateAlgebra (Fin n) K) :=
  ∏ i : Fin (n + 1), shearPolynomial n b i ^ d i

theorem shearMonomialPolynomial_monic (n : ℕ) {b : ℕ} (hb : 0 < b)
    (d : Fin (n + 1) →₀ ℕ) : (shearMonomialPolynomial (K := K) n b d).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun i _ => (shearPolynomial_monic n hb i).pow _)

theorem shearMonomialPolynomial_natDegree (n : ℕ) {b : ℕ} (hb : 0 < b)
    (d : Fin (n + 1) →₀ ℕ) :
    (shearMonomialPolynomial (K := K) n b d).natDegree = baseWeight b d := by
  rw [shearMonomialPolynomial, Polynomial.natDegree_prod_of_monic Finset.univ
    (fun i => shearPolynomial (K := K) n b i ^ d i)
    (fun i _ => (shearPolynomial_monic n hb i).pow _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [(shearPolynomial_monic n hb i).natDegree_pow, shearPolynomial_natDegree]

variable [CompleteSpace K]

/-- The composite is built from the genuine analytic substitution and the
proved restricted-series regrouping equivalence. -/
def regroupShearHom (n b : ℕ) :
    StrictTateAlgebra (Fin (n + 1)) K →+*
      RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K) :=
  (regroupEquiv (A := K) n).toRingHom.comp
    (powerShear (K := K) (0 : Fin (n + 1)) (fun i => b ^ (i : ℕ))).toRingHom

theorem regroupShearHom_X (n b : ℕ) (i : Fin (n + 1)) :
    regroupShearHom (K := K) n b (X (Fin (n + 1)) K i) =
      RestrictedSeries.ofPolynomial _ (shearPolynomial n b i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change regroupEquiv n
      (powerShear (K := K) 0 (fun i : Fin (n + 1) => b ^ (i : ℕ))
        (X (Fin (n + 1)) K 0)) = _
    rw [powerShear_pivot]
    exact regroup_X_zero n
  · change regroupEquiv n
      (powerShear (K := K) 0 (fun i : Fin (n + 1) => b ^ (i : ℕ))
        (X (Fin (n + 1)) K j.succ)) = _
    rw [powerShear_other _ _ _ (Fin.succ_ne_zero j), map_add, map_pow,
      regroup_X_succ, regroup_X_zero]
    change algebraMap _ _ (X (Fin n) K j) +
      RestrictedSeries.ofPolynomial _ Polynomial.X ^ (b ^ ((j : ℕ) + 1)) =
        RestrictedSeries.ofPolynomial _
          (Polynomial.X ^ (b ^ ((j : ℕ) + 1)) + Polynomial.C (X (Fin n) K j))
    rw [map_add, map_pow]
    change _ = _ + RestrictedSeries.ofPolynomial (StrictTateAlgebra (Fin n) K)
      (algebraMap (StrictTateAlgebra (Fin n) K)
        (Polynomial (StrictTateAlgebra (Fin n) K)) (X (Fin n) K j))
    rw [AlgHom.commutes]
    exact add_comm _ _

theorem regroupShearHom_algebraMap (n b : ℕ) (a : K) :
    regroupShearHom (K := K) n b
      (algebraMap K (StrictTateAlgebra (Fin (n + 1)) K) a) =
      RestrictedSeries.ofPolynomial _
        (Polynomial.C (algebraMap K (StrictTateAlgebra (Fin n) K) a)) := by
  change regroupEquiv n ((powerShear (K := K) 0
    (fun i : Fin (n + 1) => b ^ (i : ℕ))) (algebraMap K _ a)) = _
  rw [AlgEquiv.commutes]
  calc
    _ = algebraMap (StrictTateAlgebra (Fin n) K)
        (RestrictedSeries.Algebra (StrictTateAlgebra (Fin n) K))
        (algebraMap K (StrictTateAlgebra (Fin n) K) a) := regroup_algebraMap n a
    _ = _ := (AlgHom.commutes (RestrictedSeries.ofPolynomial _) _).symm

/-- A sheared monomial is the indicated genuine polynomial, not an assumed
polynomial representative of an analytic image. -/
theorem regroupShearHom_monomial (n b : ℕ) (d : Fin (n + 1) →₀ ℕ) (a : K) :
    regroupShearHom (K := K) n b (monomial (Fin (n + 1)) K d a) =
      RestrictedSeries.ofPolynomial _
        (Polynomial.C (algebraMap K (StrictTateAlgebra (Fin n) K) a) *
          shearMonomialPolynomial n b d) := by
  classical
  rw [monomial_eq, map_mul, regroupShearHom_algebraMap, map_mul]
  congr 1
  unfold monomialValue shearMonomialPolynomial
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow, map_pow, regroupShearHom_X]

end Langlands.Analytic.StrictTateAlgebra
