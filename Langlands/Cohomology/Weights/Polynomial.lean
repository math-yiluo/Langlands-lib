import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Polynomial weight factors

The complex polynomial construction underlying the separation by weights in
Kottwitz (1992), Theorem 1 and Section 6. This file does not construct Shimura
cohomology, a Galois representation, or descent of a factor to a number field.
-/

noncomputable section

open Polynomial
open scoped Classical

namespace Langlands.Cohomology.Weights

/-- The absolute value of an eigenvalue of integral weight `w` over a residue
field of cardinality `q`. Applications require `1 < q`. -/
def radius (q : ℕ) (w : ℤ) : ℝ :=
  (q : ℝ) ^ ((w : ℝ) / 2)

/-- The weight condition for one complex value. This alone asserts neither
algebraicity nor a condition on its conjugates. -/
def HasComplexWeight (q : ℕ) (w : ℤ) (z : ℂ) : Prop :=
  ‖z‖ = radius q w

/-- Algebraicity and the weight condition at every conjugate over `ℚ`.
Conjugates are expressed as the complex zeros of the actual minimal polynomial. -/
def IsWeilNumber (q : ℕ) (w : ℤ) (z : ℂ) : Prop :=
  IsAlgebraic ℚ z ∧
    ∀ z' : ℂ, aeval z' (minpoly ℚ z) = 0 → HasComplexWeight q w z'

/-- All roots have the indicated absolute value at the chosen complex
realization. The constant polynomial `1` satisfies this condition. -/
def HasComplexRootsOfWeight (q : ℕ) (w : ℤ) (P : ℂ[X]) : Prop :=
  ∀ z ∈ P.roots, HasComplexWeight q w z

/-- A monic polynomial over a number field whose complex roots are Weil numbers
of the indicated weight, at every embedding of its coefficient field. -/
def IsPurePolynomial {L : Type*} [Field L] [NumberField L]
    (q : ℕ) (w : ℤ) (P : L[X]) : Prop :=
  P.Monic ∧ ∀ (ι : L →+* ℂ) (z : ℂ), z ∈ (P.map ι).roots → IsWeilNumber q w z

theorem IsWeilNumber.hasComplexWeight {q : ℕ} {w : ℤ} {z : ℂ}
    (h : IsWeilNumber q w z) : HasComplexWeight q w z :=
  h.2 z (minpoly.aeval ℚ z)

theorem IsPurePolynomial.hasComplexRootsOfWeight {L : Type*}
    [Field L] [NumberField L] {q : ℕ} {w : ℤ} {P : L[X]}
    (h : IsPurePolynomial q w P) (ι : L →+* ℂ) :
    HasComplexRootsOfWeight q w (P.map ι) :=
  fun z hz => (h.2 ι z hz).hasComplexWeight

theorem radius_injective {q : ℕ} (hq : 1 < q) :
    Function.Injective (radius q) := by
  intro u v huv
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have h := (Real.strictMono_rpow_of_base_gt_one hq').injective huv
  change (u : ℝ) / 2 = (v : ℝ) / 2 at h
  have huv' : (u : ℝ) = v := by linarith
  exact_mod_cast huv'

theorem HasComplexWeight.unique {q : ℕ} (hq : 1 < q) {u v : ℤ} {z : ℂ}
    (hu : HasComplexWeight q u z) (hv : HasComplexWeight q v z) : u = v :=
  radius_injective hq (hu.symm.trans hv)

/-- Retain precisely the roots of weight `w`, with their original multiplicities.
This is an actual monic complex polynomial, formed as a finite product. -/
def complexWeightFactor (q : ℕ) (w : ℤ) (P : ℂ[X]) : ℂ[X] :=
  ((P.roots.filter (HasComplexWeight q w)).map fun z => X - C z).prod

/-- The complementary monic factor at the same complex realization. -/
def complexWeightComplement (q : ℕ) (w : ℤ) (P : ℂ[X]) : ℂ[X] :=
  ((P.roots.filter fun z => ¬ HasComplexWeight q w z).map fun z => X - C z).prod

theorem complexWeightFactor_monic (q : ℕ) (w : ℤ) (P : ℂ[X]) :
    (complexWeightFactor q w P).Monic :=
  monic_multisetProd_X_sub_C _

theorem complexWeightComplement_monic (q : ℕ) (w : ℤ) (P : ℂ[X]) :
    (complexWeightComplement q w P).Monic :=
  monic_multisetProd_X_sub_C _

theorem roots_complexWeightFactor (q : ℕ) (w : ℤ) (P : ℂ[X]) :
    (complexWeightFactor q w P).roots = P.roots.filter (HasComplexWeight q w) :=
  roots_multiset_prod_X_sub_C _

theorem roots_complexWeightComplement (q : ℕ) (w : ℤ) (P : ℂ[X]) :
    (complexWeightComplement q w P).roots =
      P.roots.filter (fun z => ¬ HasComplexWeight q w z) :=
  roots_multiset_prod_X_sub_C _

theorem complexWeightFactor_hasComplexRootsOfWeight (q : ℕ) (w : ℤ) (P : ℂ[X]) :
    HasComplexRootsOfWeight q w (complexWeightFactor q w P) := by
  intro z hz
  rw [roots_complexWeightFactor] at hz
  exact (Multiset.mem_filter.mp hz).2

theorem complexWeightFactor_mul_complement (q : ℕ) (w : ℤ) {P : ℂ[X]}
    (hP : P.Monic) :
    complexWeightFactor q w P * complexWeightComplement q w P = P := by
  classical
  unfold complexWeightFactor complexWeightComplement
  rw [← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not]
  exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP
    IsAlgClosed.card_roots_eq_natDegree

theorem complexWeightFactor_eq_self {q : ℕ} {w : ℤ} {P : ℂ[X]}
    (hP : P.Monic) (hw : HasComplexRootsOfWeight q w P) :
    complexWeightFactor q w P = P := by
  classical
  unfold complexWeightFactor
  rw [Multiset.filter_eq_self.mpr hw]
  exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP
    IsAlgClosed.card_roots_eq_natDegree

theorem complexWeightFactor_eq_one {q : ℕ} {w : ℤ} {P : ℂ[X]}
    (hw : ∀ z ∈ P.roots, ¬ HasComplexWeight q w z) :
    complexWeightFactor q w P = 1 := by
  classical
  simp only [complexWeightFactor, Multiset.filter_eq_nil.mpr hw,
    Multiset.map_zero, Multiset.prod_zero]

theorem complexWeightFactor_different_weight {q : ℕ} (hq : 1 < q)
    {u v : ℤ} (huv : u ≠ v) {P : ℂ[X]} (hP : HasComplexRootsOfWeight q v P) :
    complexWeightFactor q u P = 1 :=
  complexWeightFactor_eq_one fun z hz hzu => huv (hzu.unique hq (hP z hz))

theorem complexWeightFactor_idempotent (q : ℕ) (w : ℤ) (P : ℂ[X]) :
    complexWeightFactor q w (complexWeightFactor q w P) =
      complexWeightFactor q w P :=
  complexWeightFactor_eq_self (complexWeightFactor_monic q w P)
    (complexWeightFactor_hasComplexRootsOfWeight q w P)

theorem complexWeightFactor_mul (q : ℕ) (w : ℤ) {P Q : ℂ[X]}
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    complexWeightFactor q w (P * Q) =
      complexWeightFactor q w P * complexWeightFactor q w Q := by
  classical
  simp only [complexWeightFactor, roots_mul (mul_ne_zero hP hQ),
    Multiset.filter_add, Multiset.map_add, Multiset.prod_add]

theorem complexWeightFactor_one (q : ℕ) (w : ℤ) :
    complexWeightFactor q w 1 = 1 := by
  simp [complexWeightFactor]

theorem complexWeightFactor_pow (q : ℕ) (w : ℤ) (P : ℂ[X]) (m : ℕ) :
    complexWeightFactor q w (P ^ m) = complexWeightFactor q w P ^ m := by
  classical
  induction m with
  | zero => simp [complexWeightFactor_one]
  | succ m ih =>
    by_cases hP : P = 0
    · subst P
      simp [complexWeightFactor]
    · rw [pow_succ, complexWeightFactor_mul q w (pow_ne_zero m hP) hP, ih, pow_succ]

end Langlands.Cohomology.Weights
