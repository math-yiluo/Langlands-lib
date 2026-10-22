import Langlands.Cohomology.Weights.Polynomial
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Unitary normalization of Euler polynomials

This is a complex polynomial construction. It does not assert that a
half-weight normalization is a lambda-adic Galois representation.
-/

noncomputable section

namespace Langlands.GaloisRepresentation

open Polynomial

/-- Normalize a nonzero eigenvalue to absolute value one. At zero this
total function is zero; the source applications have no zero eigenvalues. -/
def unitaryRoot (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem norm_unitaryRoot {z : ℂ} (hz : z ≠ 0) : ‖unitaryRoot z‖ = 1 := by
  simp [unitaryRoot, norm_ne_zero_iff.mpr hz]

theorem unitaryRoot_eq_of_weight {q : ℕ} {w : ℤ} {z : ℂ}
    (hz : Cohomology.Weights.HasComplexWeight q w z) :
    unitaryRoot z = z / (Cohomology.Weights.radius q w : ℂ) := by
  rw [unitaryRoot, hz]

/-- Euler polynomial of a multiset of eigenvalues; multiplicities are retained. -/
def eulerFromRoots (s : Multiset ℂ) : ℂ[X] :=
  (s.map fun z => 1 - C z * X).prod

theorem eulerFromRoots_add (s t : Multiset ℂ) :
    eulerFromRoots (s + t) = eulerFromRoots s * eulerFromRoots t := by
  simp [eulerFromRoots]

theorem reverse_X_sub_C (z : ℂ) :
    (X - C z).reverse = 1 - C z * X := by
  simp [Polynomial.reverse]

theorem eulerFromRoots_eq_reverse_product (s : Multiset ℂ) :
    eulerFromRoots s = ((s.map fun z => X - C z).prod).reverse := by
  induction s using Multiset.induction_on with
  | empty => simp [eulerFromRoots, Polynomial.reverse]
  | cons z s ih =>
    simpa only [eulerFromRoots, Multiset.map_cons, Multiset.prod_cons,
      reverse_mul_of_domain, reverse_X_sub_C] using
      congrArg (fun P => (1 - C z * X) * P) ih

theorem eulerFromRoots_eq_reverse {P : ℂ[X]} (hP : P.Monic) :
    eulerFromRoots P.roots = P.reverse := by
  rw [eulerFromRoots_eq_reverse_product,
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP
      IsAlgClosed.card_roots_eq_natDegree]

/-- The monic polynomial with normalized eigenvalues as roots. -/
def unitaryEigenvaluePolynomial (P : ℂ[X]) : ℂ[X] :=
  ((P.roots.map unitaryRoot).map fun z => X - C z).prod

/-- The normalized Euler polynomial from an eigenvalue polynomial. -/
def unitaryEulerFromEigenvalues (P : ℂ[X]) : ℂ[X] :=
  (unitaryEigenvaluePolynomial P).reverse

/-- Harris's normalization of an Euler polynomial: its reciprocal roots
are eigenvalues, each of which is divided by its own complex absolute value. -/
def unitaryEulerPolynomial (P : ℂ[X]) : ℂ[X] :=
  unitaryEulerFromEigenvalues P.reverse

theorem unitaryEigenvaluePolynomial_monic (P : ℂ[X]) :
    (unitaryEigenvaluePolynomial P).Monic :=
  monic_multisetProd_X_sub_C _

theorem roots_unitaryEigenvaluePolynomial (P : ℂ[X]) :
    (unitaryEigenvaluePolynomial P).roots = P.roots.map unitaryRoot :=
  roots_multiset_prod_X_sub_C _

theorem unitaryEulerFromEigenvalues_formula (P : ℂ[X]) :
    unitaryEulerFromEigenvalues P = eulerFromRoots (P.roots.map unitaryRoot) := by
  exact (eulerFromRoots_eq_reverse_product _).symm

theorem unitaryEulerPolynomial_formula (P : ℂ[X]) :
    unitaryEulerPolynomial P = eulerFromRoots (P.reverse.roots.map unitaryRoot) :=
  unitaryEulerFromEigenvalues_formula _

theorem unitaryEulerFromEigenvalues_coeff_zero (P : ℂ[X]) :
    (unitaryEulerFromEigenvalues P).coeff 0 = 1 := by
  rw [unitaryEulerFromEigenvalues, coeff_zero_reverse,
    (unitaryEigenvaluePolynomial_monic P).leadingCoeff]

theorem unitaryEulerPolynomial_coeff_zero (P : ℂ[X]) :
    (unitaryEulerPolynomial P).coeff 0 = 1 :=
  unitaryEulerFromEigenvalues_coeff_zero _

theorem roots_unitaryEigenvaluePolynomial_norm {P : ℂ[X]}
    (hP : P.coeff 0 ≠ 0) {z : ℂ}
    (hz : z ∈ (unitaryEigenvaluePolynomial P).roots) : ‖z‖ = 1 := by
  rw [roots_unitaryEigenvaluePolynomial, Multiset.mem_map] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  apply norm_unitaryRoot
  intro ha0
  subst a
  apply hP
  simpa only [IsRoot, ← coeff_zero_eq_eval_zero] using isRoot_of_mem_roots ha

theorem unitaryEigenvaluePolynomial_natDegree (P : ℂ[X]) :
    (unitaryEigenvaluePolynomial P).natDegree = P.natDegree := by
  rw [unitaryEigenvaluePolynomial, natDegree_multiset_prod_X_sub_C_eq_card,
    Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree]

theorem unitaryEigenvaluePolynomial_coeff_zero_ne {P : ℂ[X]}
    (hP : P.coeff 0 ≠ 0) :
    (unitaryEigenvaluePolynomial P).coeff 0 ≠ 0 := by
  intro hz
  have hroot : (0 : ℂ) ∈ (unitaryEigenvaluePolynomial P).roots := by
    apply (mem_roots (unitaryEigenvaluePolynomial_monic P).ne_zero).mpr
    simpa only [IsRoot, ← coeff_zero_eq_eval_zero] using hz
  have h := roots_unitaryEigenvaluePolynomial_norm hP hroot
  norm_num at h

theorem unitaryEulerFromEigenvalues_natDegree {P : ℂ[X]}
    (hP : P.coeff 0 ≠ 0) :
    (unitaryEulerFromEigenvalues P).natDegree = P.natDegree := by
  rw [unitaryEulerFromEigenvalues, reverse_natDegree,
    natTrailingDegree_eq_zero.mpr
      (Or.inr (unitaryEigenvaluePolynomial_coeff_zero_ne hP)),
    Nat.sub_zero, unitaryEigenvaluePolynomial_natDegree]

theorem unitaryEulerPolynomial_natDegree {P : ℂ[X]}
    (hP : P.coeff 0 ≠ 0) :
    (unitaryEulerPolynomial P).natDegree = P.natDegree := by
  have hP0 : P ≠ 0 := by
    intro hz
    exact hP (by rw [hz, coeff_zero])
  have hr : P.reverse.coeff 0 ≠ 0 := by
    rw [coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr hP0
  rw [unitaryEulerPolynomial, unitaryEulerFromEigenvalues_natDegree hr,
    reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hP), Nat.sub_zero]

theorem unitaryEigenvaluePolynomial_mul {P Q : ℂ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    unitaryEigenvaluePolynomial (P * Q) =
      unitaryEigenvaluePolynomial P * unitaryEigenvaluePolynomial Q := by
  simp [unitaryEigenvaluePolynomial, roots_mul (mul_ne_zero hP hQ)]

theorem unitaryEulerFromEigenvalues_mul {P Q : ℂ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    unitaryEulerFromEigenvalues (P * Q) =
      unitaryEulerFromEigenvalues P * unitaryEulerFromEigenvalues Q := by
  simp only [unitaryEulerFromEigenvalues, unitaryEigenvaluePolynomial_mul hP hQ,
    reverse_mul_of_domain]

theorem unitaryEulerPolynomial_mul {P Q : ℂ[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    unitaryEulerPolynomial (P * Q) =
      unitaryEulerPolynomial P * unitaryEulerPolynomial Q := by
  rw [unitaryEulerPolynomial, reverse_mul_of_domain,
    unitaryEulerFromEigenvalues_mul (mt reverse_eq_zero.mp hP) (mt reverse_eq_zero.mp hQ)]
  rfl

theorem eulerFromRoots_map_div (s : Multiset ℂ) (a : ℂ) :
    eulerFromRoots (s.map fun z => z / a) =
      (eulerFromRoots s).comp (C a⁻¹ * X) := by
  induction s using Multiset.induction_on with
  | empty => simp [eulerFromRoots]
  | cons z s ih =>
    simp only [eulerFromRoots, Multiset.map_cons, Multiset.prod_cons,
      mul_comp, sub_comp, one_comp, C_comp, X_comp] at *
    rw [ih]
    simp only [div_eq_mul_inv, map_mul]
    ring

/-- For one pure weight, normalization is substitution by the inverse weight
radius in the arithmetic Euler polynomial. No integrality of half the weight
or Galois-theoretic twist is asserted. -/
theorem unitaryEulerFromEigenvalues_eq_weight_substitution
    {q : ℕ} {w : ℤ} {P : ℂ[X]} (hP : P.Monic)
    (hw : Cohomology.Weights.HasComplexRootsOfWeight q w P) :
    unitaryEulerFromEigenvalues P =
      P.reverse.comp (C (Cohomology.Weights.radius q w : ℂ)⁻¹ * X) := by
  rw [unitaryEulerFromEigenvalues_formula]
  have hm : P.roots.map unitaryRoot =
      P.roots.map (fun z => z / (Cohomology.Weights.radius q w : ℂ)) :=
    Multiset.map_congr rfl fun z hz => unitaryRoot_eq_of_weight (hw z hz)
  rw [hm, eulerFromRoots_map_div, eulerFromRoots_eq_reverse hP]

end Langlands.GaloisRepresentation
