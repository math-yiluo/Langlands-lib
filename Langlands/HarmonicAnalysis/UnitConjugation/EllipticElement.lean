import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Idempotent

/-!
# Elliptic elements of the Lie algebra of `Aˣ`

Let `A` be a ring, regarded as the Lie algebra of its unit group `Aˣ`. An element `X ∈ A` is
*elliptic* (`IsEllipticElement X`) when every idempotent of `A` commuting with `X` is central
in `A`.

For a regular element `X` of a finite-dimensional semisimple algebra over a field of
characteristic zero (`regularSet`), the centralizer `h` of `X` in `A` is a Cartan subalgebra: a
commutative semisimple algebra, a finite product of fields, whose unit group `hˣ` is the
Cartan subgroup, the centralizer of `X` in `Aˣ`. The split component of `hˣ` is the group of
the elements `∑ tⱼ εⱼ` (`tⱼ` nonzero scalars), where `εⱼ` are the primitive idempotents of `h`.
It lies in the centre of `Aˣ` exactly when every idempotent of `h` is central in `A`, and the
idempotents of `A` commuting with `X` are those of `h`. So for regular `X` the condition is
Harish-Chandra's: the Cartan subalgebra containing `X` is elliptic.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §1, printed p. 5: "Let `A` denote the split component of the
corresponding Cartan subgroup of `G`. `h` is called elliptic if `A` lies in the center of `G`."

Basic facts: `not_isEllipticElement_iff` (a non-elliptic element commutes with a non-central
idempotent), `isEllipticElement_of_forall_commute` (in a commutative situation every element is
elliptic), and `isEllipticElement_conj_iff` (ellipticity is invariant under conjugation by
units).
-/

namespace Langlands.HarmonicAnalysis.UnitConjugation

universe v

variable {A : Type v} [Ring A]

/-- `X` is *elliptic* when every idempotent of `A` commuting with `X` is central in `A`. For a
regular element of a finite-dimensional semisimple algebra this is Harish-Chandra's ellipticity
of the Cartan subalgebra containing `X`: the split component of the centralizer of `X` in `Aˣ`
lies in the centre of `Aˣ`. -/
def IsEllipticElement (X : A) : Prop :=
  ∀ e : A, IsIdempotentElem e → e * X = X * e → ∀ a : A, e * a = a * e

/-- A non-elliptic element commutes with a non-central idempotent. -/
theorem not_isEllipticElement_iff (X : A) :
    ¬ IsEllipticElement X ↔
      ∃ e : A, IsIdempotentElem e ∧ e * X = X * e ∧ ∃ a : A, e * a ≠ a * e := by
  simp only [IsEllipticElement, not_forall, exists_prop]

/-- If all idempotents are central, every element is elliptic. -/
theorem isEllipticElement_of_forall_commute
    (h : ∀ e : A, IsIdempotentElem e → ∀ a : A, e * a = a * e) (X : A) :
    IsEllipticElement X :=
  fun e he _ => h e he

/-- Ellipticity is invariant under ring automorphisms. -/
theorem isEllipticElement_map_iff (σ : A ≃+* A) (X : A) :
    IsEllipticElement (σ X) ↔ IsEllipticElement X := by
  have key : ∀ (τ : A ≃+* A) (Y : A), IsEllipticElement Y → IsEllipticElement (τ Y) := by
    intro τ Y hY e he hc a
    have he' : IsIdempotentElem (τ.symm e) := by
      change τ.symm e * τ.symm e = τ.symm e
      rw [← map_mul, he.eq]
    have hc' : τ.symm e * Y = Y * τ.symm e := by
      apply τ.injective
      rw [map_mul, map_mul, RingEquiv.apply_symm_apply]
      exact hc
    have h := congrArg τ (hY _ he' hc' (τ.symm a))
    simpa only [map_mul, RingEquiv.apply_symm_apply] using h
  refine ⟨fun h => ?_, key σ X⟩
  simpa only [RingEquiv.symm_apply_apply] using key σ.symm _ h

/-- Ellipticity is invariant under conjugation by units. -/
theorem isEllipticElement_conj_iff (u : Aˣ) (X : A) :
    IsEllipticElement ((u : A) * X * ((u⁻¹ : Aˣ) : A)) ↔ IsEllipticElement X :=
  isEllipticElement_map_iff
    { toFun := fun x => (u : A) * x * ((u⁻¹ : Aˣ) : A)
      invFun := fun x => ((u⁻¹ : Aˣ) : A) * x * (u : A)
      left_inv := fun x => by simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul,
        mul_one]
      right_inv := fun x => by simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv,
        mul_one]
      map_mul' := fun x y => by simp only [mul_assoc, Units.inv_mul_cancel_left]
      map_add' := fun x y => by simp only [mul_add, add_mul] } X

end Langlands.HarmonicAnalysis.UnitConjugation
