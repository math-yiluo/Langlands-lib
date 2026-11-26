import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.List.OfFn

/-!
# The polynomial in the Harris–Taylor cohomological projector

Harris–Taylor III.2, p. 98 applies a product of degree-one selectors
to the multiplication-by-two endomorphisms of the factors of a relative
abelian power. This module constructs that polynomial operator and checks
its action on the simultaneous eigenspaces.
-/

noncomputable section

open Polynomial
open scoped BigOperators Polynomial

set_option autoImplicit false

namespace Langlands.Shimura.PEL.CohomologicalProjector

universe u v

/-- Over a characteristic-zero field this polynomial takes value one at `2`
and zero at the other powers `2^j` in the specified range. -/
def degreeOnePolynomial (F : Type u) [Field F] (d : ℕ) : F[X] :=
  ∏ j ∈ (Finset.range (d + 1)).erase 1,
    C (((2 : F) - 2 ^ j)⁻¹) * (X - C ((2 : F) ^ j))

variable {F : Type u} [Field F]

theorem degreeOnePolynomial_eval_two [CharZero F] (d : ℕ) :
    (degreeOnePolynomial F d).eval 2 = 1 := by
  rw [degreeOnePolynomial, eval_prod]
  apply Finset.prod_eq_one
  intro j hj
  have hj1 := (Finset.mem_erase.mp hj).1
  have h : (2 : F) - 2 ^ j ≠ 0 := by
    intro hz
    have he : (2 : F) ^ j = (2 : F) ^ 1 := by simpa using (sub_eq_zero.mp hz).symm
    have hnat : (2 : ℕ) ^ j = 2 ^ 1 := Nat.cast_injective (R := F) (by simpa using he)
    exact hj1 (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hnat)
  simp only [eval_mul, eval_C, eval_sub, eval_X, inv_mul_cancel₀ h]

theorem degreeOnePolynomial_eval_pow (d j : ℕ) (hj : j ≤ d) (hj1 : j ≠ 1) :
    (degreeOnePolynomial F d).eval (2 ^ j) = 0 := by
  rw [degreeOnePolynomial, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj1, Finset.mem_range.mpr (Nat.lt_succ_of_le hj)⟩)
  simp

/-- The product defining the selector on all factors, with the factors
composed in their given order. For zero factors this is the identity. -/
def degreeOneEndomorphism (F : Type u) [Field F] {A : Type v} [Ring A] [Algebra F A] {m : ℕ}
    (d : ℕ) (T : Fin m → A) : A :=
  (List.ofFn fun i => aeval (T i) (degreeOnePolynomial F d)).prod

section Module

variable {V : Type v} [AddCommGroup V] [Module F V]

private theorem prod_apply_of_eigenvectors {m : ℕ} (T : Fin m → Module.End F V)
    (a : Fin m → F) (x : V) (hx : ∀ i, T i x = a i • x) :
    (List.ofFn T).prod x = (List.ofFn a).prod • x := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
        Module.End.mul_apply, ih (fun i => T i.succ) (fun i => a i.succ) (fun i => hx i.succ)]
      rw [map_smul, hx 0, smul_smul, mul_comm]

/-- On a simultaneous eigenvector of weights `2^(q i)`, the full operator
keeps the vector exactly when all the degrees `q i` are one. -/
theorem degreeOneEndomorphism_apply_of_eigenvectors [CharZero F] {m d : ℕ}
    (T : Fin m → Module.End F V) (q : Fin m → Fin (d + 1)) (x : V)
    (hx : ∀ i, T i x = (2 : F) ^ (q i).val • x) :
    degreeOneEndomorphism F d T x = if ∀ i, (q i).val = 1 then x else 0 := by
  classical
  unfold degreeOneEndomorphism
  rw [prod_apply_of_eigenvectors _
    (fun i => (degreeOnePolynomial F d).eval ((2 : F) ^ (q i).val)) x
    (fun i => Module.End.aeval_apply_of_mem_apply_eq_smul (hx i))]
  by_cases hq : ∀ i, (q i).val = 1
  · simp [hq, degreeOnePolynomial_eval_two]
  · obtain ⟨i, hi⟩ := not_forall.mp hq
    have h : (0 : F) ∈ List.ofFn (fun j => (degreeOnePolynomial F d).eval ((2 : F) ^ (q j).val)) := by
      apply (List.mem_ofFn' _ _).mpr
      exact ⟨i, degreeOnePolynomial_eval_pow d (q i).val (Nat.le_of_lt_succ (q i).isLt) hi⟩
    simp [List.prod_eq_zero h, hq]

/-- The operator is idempotent on any module spanned by the permitted
simultaneous eigenspaces. -/
theorem degreeOneEndomorphism_idempotent [CharZero F] {m : ℕ}
    (d : ℕ) (T : Fin m → Module.End F V)
    (hspan : Submodule.span F {x : V | ∃ q : Fin m → Fin (d + 1),
      ∀ i, T i x = (2 : F) ^ (q i).val • x} = ⊤) :
    IsIdempotentElem (degreeOneEndomorphism F d T) := by
  apply LinearMap.ext_on hspan
  intro x hx
  obtain ⟨q, hq⟩ := hx
  change degreeOneEndomorphism F d T (degreeOneEndomorphism F d T x) =
    degreeOneEndomorphism F d T x
  classical
  have happ := degreeOneEndomorphism_apply_of_eigenvectors T q x hq
  by_cases hall : ∀ i, (q i).val = 1
  · simp [hall] at happ
    rw [happ]
    exact happ
  · simp [hall] at happ
    simp [happ]

end Module

end Langlands.Shimura.PEL.CohomologicalProjector
