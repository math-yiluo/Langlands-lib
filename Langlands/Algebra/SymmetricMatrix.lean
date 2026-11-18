import Langlands.LinearAlgebra.HomogeneousPolynomialMatrix
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! # Canonical finite monomial coordinates for symmetric matrix powers -/

noncomputable section

universe u

open Module
open scoped Matrix

namespace Langlands.Algebra.SymmetricMatrix

open Langlands.LinearAlgebra

/-- Monomials of total degree `d` in the finite coordinate set `n`. -/
abbrev Index (n : Type) (d : ℕ) := HomogeneousPolynomial.MonomialIndex n d

instance {n : Type} (d : ℕ) : DecidableEq (Index n d) := Classical.decEq _

variable (R : Type u) [CommRing R] (n : Type) (d : ℕ)

/-- The canonical monomial basis of the genuine homogeneous polynomial module. -/
def basis : Basis (Index n d) R (MvPolynomial.homogeneousSubmodule n R d) :=
  HomogeneousPolynomial.monomialBasis n d R

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem basis_apply (a : Index n d) :
    (basis R n d a : MvPolynomial n R) = MvPolynomial.monomial a.val 1 :=
  HomogeneousPolynomial.monomialBasis_val n d R a

@[simp]
theorem basis_repr (P : MvPolynomial.homogeneousSubmodule n R d) (a : Index n d) :
    (basis R n d).repr P a = (P : MvPolynomial n R).coeff a.val :=
  HomogeneousPolynomial.monomialBasis_repr n d R P a

variable {R n d} [Fintype n]

/-- Linear substitution on the polynomial algebra, acting on generators by the
columns of a matrix. -/
def substitute (M : Matrix n n R) : MvPolynomial n R →ₐ[R] MvPolynomial n R :=
  MvPolynomial.aeval fun j => ∑ i, MvPolynomial.C (M i j) * MvPolynomial.X i

@[simp]
theorem substitute_X (M : Matrix n n R) (j : n) :
    substitute M (MvPolynomial.X j) =
      ∑ i, MvPolynomial.C (M i j) * MvPolynomial.X i := by simp [substitute]

@[simp]
theorem substitute_C (M : Matrix n n R) (r : R) :
    substitute M (MvPolynomial.C r) = MvPolynomial.C r := by simp [substitute]

theorem substitute_homogeneous (M : Matrix n n R)
    {P : MvPolynomial n R} (hP : P.IsHomogeneous d) :
    (substitute M P).IsHomogeneous d := by
  simpa only [substitute, one_mul] using hP.aeval
    (fun j => ∑ i, MvPolynomial.C (M i j) * MvPolynomial.X i)
    (fun j => MvPolynomial.IsHomogeneous.sum _ _ 1 (fun i _ =>
      (MvPolynomial.isHomogeneous_X R i).C_mul (M i j)))

@[simp]
theorem substitute_one [DecidableEq n] : substitute (1 : Matrix n n R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [substitute, Matrix.one_apply, ite_mul]

theorem substitute_mul (M N : Matrix n n R) :
    substitute (M * N) = (substitute M).comp (substitute N) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [substitute_X, AlgHom.comp_apply, map_sum, map_mul, substitute_C,
    Matrix.mul_apply]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- An arbitrary matrix acts on each homogeneous polynomial module. -/
def action (M : Matrix n n R) :
    Module.End R (MvPolynomial.homogeneousSubmodule n R d) :=
  HomogeneousPolynomial.action M d

@[simp]
theorem action_apply (M : Matrix n n R)
    (P : MvPolynomial.homogeneousSubmodule n R d) :
    (action M P : MvPolynomial n R) = substitute M P := rfl

@[simp]
theorem action_one [DecidableEq n] : action (d := d) (1 : Matrix n n R) = 1 :=
  HomogeneousPolynomial.action_one d

theorem action_mul (M N : Matrix n n R) :
    action (d := d) (M * N) = action M * action N :=
  HomogeneousPolynomial.action_mul M N d

/-- The symmetric matrix in canonical degree-`d` monomial coordinates. -/
def matrix (M : Matrix n n R) (d : ℕ) : Matrix (Index n d) (Index n d) R :=
  LinearMap.toMatrix (basis R n d) (basis R n d) (action M)

@[simp]
theorem matrix_apply (M : Matrix n n R) (a b : Index n d) :
    matrix M d a b = (substitute M (MvPolynomial.monomial b.val 1)).coeff a.val := by
  simp [matrix, LinearMap.toMatrix_apply]

@[simp]
theorem matrix_one [DecidableEq n] : matrix (1 : Matrix n n R) d = 1 := by
  simp [matrix]

theorem matrix_mul (M N : Matrix n n R) :
    matrix (M * N) d = matrix M d * matrix N d := by
  unfold matrix
  rw [action_mul, LinearMap.toMatrix_mul]

/-- Monomial coordinates of a homogeneous polynomial are its coefficients. -/
@[simp]
theorem basis_equivFun_apply (P : MvPolynomial.homogeneousSubmodule n R d)
    (a : Index n d) : (basis R n d).equivFun P a =
      (P : MvPolynomial n R).coeff a.val := rfl

/-- The symmetric matrix realizes substitution in the canonical finite basis. -/
theorem matrix_mulVec (M : Matrix n n R)
    (P : MvPolynomial.homogeneousSubmodule n R d) :
    matrix M d *ᵥ (basis R n d).equivFun P =
      (basis R n d).equivFun (action M P) := by
  exact (action M).toMatrix_mulVec_repr (basis R n d) (basis R n d) P

/-- Linear substitution commutes with an arbitrary coefficient-ring map. -/
theorem substitute_map {S : Type*} [CommRing S] (g : R →+* S)
    (M : Matrix n n R) (P : MvPolynomial n R) :
    MvPolynomial.map g (substitute M P) =
      substitute (M.map g) (MvPolynomial.map g P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP =>
    simp only [map_mul, hP, substitute_X, MvPolynomial.map_X, map_sum,
      MvPolynomial.map_C, Matrix.map_apply]

/-- Symmetric matrices commute with arbitrary coefficient-ring maps. -/
theorem matrix_map {S : Type*} [CommRing S] (g : R →+* S) (M : Matrix n n R) :
    matrix (M.map g) d = (matrix M d).map g := by
  ext a b
  simp only [Matrix.map_apply, matrix_apply]
  have h := congrArg (fun P : MvPolynomial n S => P.coeff a.val)
    (substitute_map g M (MvPolynomial.monomial b.val 1))
  simpa only [MvPolynomial.coeff_map, MvPolynomial.map_monomial, map_one] using h.symm

variable [DecidableEq n]

/-- The degree-`d` symmetric matrix construction as a multiplicative map. -/
def hom (R : Type u) [CommRing R] (n : Type) [Fintype n] [DecidableEq n] (d : ℕ) :
    Matrix n n R →* Matrix (Index n d) (Index n d) R where
  toFun M := matrix M d
  map_one' := matrix_one
  map_mul' M N := matrix_mul M N

/-- An invertible matrix acts invertibly in every degree. -/
def glHom (R : Type u) [CommRing R] (n : Type) [Fintype n] [DecidableEq n] (d : ℕ) :
    GL n R →* GL (Index n d) R :=
  ((hom R n d).comp (Units.coeHom (Matrix n n R))).toHomUnits

@[simp]
theorem glHom_val (M : GL n R) :
    (glHom R n d M : Matrix (Index n d) (Index n d) R) =
      matrix (M : Matrix n n R) d := rfl

/-- The general-linear symmetric action is natural over all rings, including
rings with nilpotents. -/
theorem glHom_map {S : Type*} [CommRing S] (g : R →+* S) (M : GL n R) :
    glHom S n d (Matrix.GeneralLinearGroup.map g M) =
      Matrix.GeneralLinearGroup.map g (glHom R n d M) := by
  apply Units.ext
  exact matrix_map g (M : Matrix n n R)

end Langlands.Algebra.SymmetricMatrix
