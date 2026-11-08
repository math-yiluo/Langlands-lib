import Langlands.Shimura.DecompositionGroupAction
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Frobenius polynomials of Galois actions on finite free modules

For an action of the absolute Galois group of a number field `K` on a finite free module over a
commutative ring `R`, the characteristic polynomial `det(X - Frob_v)` and the Euler polynomial
`det(1 - Frob_v X)` of the geometric Frobenius endomorphism at a finite place `v` are defined.
They do not depend on the closure embedding used to restrict to the decomposition group, and for
actions unramified at `v` every geometric Frobenius lift has the same characteristic polynomial.
See `FrobeniusPolynomial.md`.
-/

noncomputable section

universe u uV uK

set_option autoImplicit false

namespace Langlands.Shimura.FrobeniusPolynomial

open CategoryTheory Polynomial
open Langlands.GaloisRepresentation (ClosureEmbedding chosenClosureEmbedding LocalGroup
  IsGeometricFrobeniusLift)
open Langlands.Shimura.DecompositionGroupAction

variable {R : Type u} [CommRing R]

/-! ## Linear algebra -/

section LinearAlgebra

variable {A : Type uV} {B : Type uV} [AddCommGroup A] [Module R A] [Module.Free R A]
  [Module.Finite R A] [AddCommGroup B] [Module R B] [Module.Free R B] [Module.Finite R B]

/-- Endomorphisms intertwined by a linear equivalence have the same characteristic polynomial. -/
theorem charpoly_eq_of_comp_eq (e : A ≃ₗ[R] B) {f : Module.End R A} {g : Module.End R B}
    (h : (e : A →ₗ[R] B) ∘ₗ f = g ∘ₗ (e : A →ₗ[R] B)) : f.charpoly = g.charpoly := by
  have hconj : e.conj f = g := by
    ext x
    have hx := congrArg (fun φ : A →ₗ[R] B => φ (e.symm x)) h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hx
    rw [LinearEquiv.conj_apply_apply, hx]
  rw [← hconj, LinearEquiv.charpoly_conj]

/-- The constant coefficient of the characteristic polynomial of an automorphism is a unit. -/
theorem isUnit_charpoly_coeff_zero (e : A ≃ₗ[R] A) :
    IsUnit ((e : Module.End R A).charpoly.coeff 0) := by
  have hdet := LinearMap.det_eq_sign_charpoly_coeff (e : Module.End R A)
  have hsq : ((-1 : R) ^ Module.finrank R A) * (-1) ^ Module.finrank R A = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hc : (e : Module.End R A).charpoly.coeff 0 =
      (-1) ^ Module.finrank R A * LinearMap.det (e : Module.End R A) := by
    rw [hdet, ← mul_assoc, hsq, one_mul]
  rw [hc]
  exact ((isUnit_neg_one (α := R)).pow _).mul e.isUnit_det'

end LinearAlgebra

variable {K : Type uK} [Field K] [NumberField K] (v : Global.FinitePlace K)
  (M : Action (ModuleCat.{uV} R) (Field.absoluteGaloisGroup K))

/-! ## The Galois action as linear automorphisms -/

omit [NumberField K] in
/-- The linear automorphism by which an element of `Gal(K̄/K)` acts. -/
def actionEquiv (g : Field.absoluteGaloisGroup K) : M.V ≃ₗ[R] M.V :=
  (M.ρAut g).toLinearEquiv

omit [NumberField K] in
@[simp] theorem actionEquiv_coe (g : Field.absoluteGaloisGroup K) :
    (actionEquiv M g : M.V →ₗ[R] M.V) = (M.ρ g).hom :=
  rfl

variable [Module.Free R M.V] [Module.Finite R M.V]

/-! ## Characteristic and Euler polynomials -/

/-- The characteristic polynomial `det(X - Frob_v)` of the geometric Frobenius endomorphism at
`v`, computed along Mathlib's chosen closure embedding. -/
def frobeniusCharpoly : R[X] :=
  (geometricFrobenius (ModuleCat.{uV} R) v M
    (chosenClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))).hom.charpoly

/-- The Euler polynomial `det(1 - Frob_v X)`, the reverse of the characteristic polynomial. -/
def frobeniusEulerPolynomial : R[X] :=
  (frobeniusCharpoly v M).reverse

variable {v M}

/-- The characteristic polynomial does not depend on the closure embedding. -/
theorem frobeniusCharpoly_eq_along
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    frobeniusCharpoly v M = (geometricFrobenius (ModuleCat.{uV} R) v M ι).hom.charpoly := by
  refine charpoly_eq_of_comp_eq
    (actionEquiv M (localClosureChange v ι
      (chosenClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)))) ?_
  rw [actionEquiv_coe, ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, geometricFrobenius_conj]

/-- For an action unramified at `v`, every geometric Frobenius lift, along every closure
embedding, has the Frobenius characteristic polynomial. -/
theorem charpoly_eq_frobeniusCharpoly_of_lift
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hM : IsUnramifiedAlong (ModuleCat.{uV} R) v M ι) {g : LocalGroup v}
    (hg : IsGeometricFrobeniusLift v g) :
    (M.ρ (localRestriction v ι g)).hom.charpoly = frobeniusCharpoly v M := by
  have h : M.ρ (localRestriction v ι g) = geometricFrobenius (ModuleCat.{uV} R) v M ι :=
    geometricFrobenius_eq_of_lift hM hg
  rw [h, frobeniusCharpoly_eq_along ι]

theorem frobeniusEulerPolynomial_eq_along
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) :
    frobeniusEulerPolynomial v M =
      (geometricFrobenius (ModuleCat.{uV} R) v M ι).hom.charpoly.reverse := by
  rw [frobeniusEulerPolynomial, frobeniusCharpoly_eq_along ι]

theorem eulerPolynomial_eq_frobeniusEulerPolynomial_of_lift
    {ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)}
    (hM : IsUnramifiedAlong (ModuleCat.{uV} R) v M ι) {g : LocalGroup v}
    (hg : IsGeometricFrobeniusLift v g) :
    (M.ρ (localRestriction v ι g)).hom.charpoly.reverse = frobeniusEulerPolynomial v M := by
  rw [charpoly_eq_frobeniusCharpoly_of_lift hM hg]
  rfl

variable (v M)

theorem frobeniusCharpoly_monic : (frobeniusCharpoly v M).Monic :=
  LinearMap.charpoly_monic _

theorem frobeniusCharpoly_natDegree [Nontrivial R] :
    (frobeniusCharpoly v M).natDegree = Module.finrank R M.V :=
  LinearMap.charpoly_natDegree _

/-- The geometric Frobenius endomorphism is invertible, so the constant coefficient of its
characteristic polynomial is a unit. -/
theorem isUnit_frobeniusCharpoly_coeff_zero : IsUnit ((frobeniusCharpoly v M).coeff 0) :=
  isUnit_charpoly_coeff_zero (actionEquiv M _)

theorem frobeniusEulerPolynomial_coeff_zero : (frobeniusEulerPolynomial v M).coeff 0 = 1 := by
  rw [frobeniusEulerPolynomial, Polynomial.coeff_zero_reverse,
    (frobeniusCharpoly_monic v M).leadingCoeff]

theorem frobeniusEulerPolynomial_natDegree [Nontrivial R] :
    (frobeniusEulerPolynomial v M).natDegree = Module.finrank R M.V := by
  rw [frobeniusEulerPolynomial, Polynomial.reverse_natDegree,
    Polynomial.natTrailingDegree_eq_zero.mpr
      (Or.inr (isUnit_frobeniusCharpoly_coeff_zero v M).ne_zero),
    Nat.sub_zero, frobeniusCharpoly_natDegree]

/-- Reversing the Euler polynomial recovers the characteristic polynomial. -/
theorem reverse_frobeniusEulerPolynomial [Nontrivial R] :
    (frobeniusEulerPolynomial v M).reverse = frobeniusCharpoly v M := by
  change Polynomial.reflect (frobeniusEulerPolynomial v M).natDegree
    (Polynomial.reflect (frobeniusCharpoly v M).natDegree (frobeniusCharpoly v M)) =
      frobeniusCharpoly v M
  rw [frobeniusEulerPolynomial_natDegree, frobeniusCharpoly_natDegree, Polynomial.reflect_reflect]

/-- The Euler polynomial is `det(1 - X Frob_v)` in the matrix of the Frobenius endomorphism along
any closure embedding, in any finite basis. -/
theorem frobeniusEulerPolynomial_eq_det
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))
    {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n R M.V) :
    frobeniusEulerPolynomial v M =
      Matrix.det (1 - (X : R[X]) •
        (LinearMap.toMatrix b b (geometricFrobenius (ModuleCat.{uV} R) v M ι).hom).map C) := by
  rw [frobeniusEulerPolynomial_eq_along ι, ← LinearMap.charpoly_toMatrix _ b,
    Matrix.reverse_charpoly, Matrix.charpolyRev]

/-! ## Invariance under isomorphism -/

variable {M}

theorem frobeniusCharpoly_eq_of_iso {N : Action (ModuleCat.{uV} R) (Field.absoluteGaloisGroup K)}
    [Module.Free R N.V] [Module.Finite R N.V] (e : M ≅ N) :
    frobeniusCharpoly v M = frobeniusCharpoly v N := by
  refine charpoly_eq_of_comp_eq (A := M.V) (B := N.V)
    (Iso.toLinearEquiv (X := M.V) (Y := N.V) ((Action.forget _ _).mapIso e)) ?_
  change (e.hom.hom).hom ∘ₗ _ = _ ∘ₗ (e.hom.hom).hom
  rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, geometricFrobenius_naturality]

theorem frobeniusEulerPolynomial_eq_of_iso
    {N : Action (ModuleCat.{uV} R) (Field.absoluteGaloisGroup K)}
    [Module.Free R N.V] [Module.Finite R N.V] (e : M ≅ N) :
    frobeniusEulerPolynomial v M = frobeniusEulerPolynomial v N := by
  rw [frobeniusEulerPolynomial, frobeniusEulerPolynomial, frobeniusCharpoly_eq_of_iso v e]

end Langlands.Shimura.FrobeniusPolynomial
