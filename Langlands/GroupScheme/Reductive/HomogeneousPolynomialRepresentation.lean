import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RepresentationTheory.Basic

/-! # Matrix representations on homogeneous polynomials in every degree -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.HomogeneousPolynomial

open MvPolynomial Matrix

variable {n : Type u} [Fintype n]
  {R : Type v} [CommSemiring R]

/-- The linear form specified by the `i`th column of a matrix. -/
def variableImage (A : Matrix n n R) (i : n) : MvPolynomial n R :=
  ∑ j, C (A j i) * X j

/-- Substitution of the matrix columns for the polynomial variables. -/
def substitution (A : Matrix n n R) :
    MvPolynomial n R →ₐ[R] MvPolynomial n R :=
  aeval (variableImage A)

@[simp]
theorem substitution_X (A : Matrix n n R) (i : n) :
    substitution A (X i) = variableImage A i :=
  aeval_X _ _

@[simp]
theorem substitution_C (A : Matrix n n R) (r : R) :
    substitution A (C r) = C r :=
  aeval_C _ _

theorem variableImage_homogeneous (A : Matrix n n R) (i : n) :
    (variableImage A i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ j)

variable [DecidableEq n]

@[simp]
theorem variableImage_one (i : n) :
    variableImage (1 : Matrix n n R) i = X i := by
  classical
  simp [variableImage, Matrix.one_apply]

@[simp]
theorem substitution_one :
    substitution (1 : Matrix n n R) = AlgHom.id R (MvPolynomial n R) := by
  ext i
  simp

omit [DecidableEq n] in
/-- Column substitution is covariant in matrix multiplication. -/
theorem substitution_mul (A B : Matrix n n R) :
    substitution (A * B) = (substitution A).comp (substitution B) := by
  ext i
  simp only [AlgHom.comp_apply, substitution_X, variableImage, Matrix.mul_apply,
    map_sum, map_mul, substitution_C, substitution_X, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext j
  congr 1
  ext k
  simp [mul_left_comm, mul_comm]

omit [DecidableEq n] in
/-- Matrix substitution preserves the homogeneous degree, including degree zero. -/
theorem substitution_homogeneous (A : Matrix n n R) {m : ℕ}
    {p : MvPolynomial n R} (hp : p.IsHomogeneous m) :
    (substitution A p).IsHomogeneous m := by
  simpa only [substitution, one_mul] using
    hp.aeval (variableImage A) (variableImage_homogeneous A)

/-- The actual operator on the homogeneous submodule of degree `m`. -/
def homogeneousMap (m : ℕ) (A : Matrix n n R) :
    homogeneousSubmodule n R m →ₗ[R] homogeneousSubmodule n R m where
  toFun p := ⟨substitution A p, substitution_homogeneous A p.property⟩
  map_add' p q := Subtype.ext (map_add (substitution A)
    (p : MvPolynomial n R) (q : MvPolynomial n R))
  map_smul' r p := Subtype.ext ((substitution A).toLinearMap.map_smul r
    (p : MvPolynomial n R))

omit [DecidableEq n] in
@[simp]
theorem homogeneousMap_coe (m : ℕ) (A : Matrix n n R)
    (p : homogeneousSubmodule n R m) :
    (homogeneousMap m A p : MvPolynomial n R) = substitution A p :=
  rfl

/-- The matrix monoid acts on homogeneous polynomials in every degree. -/
def matrixRepresentation (m : ℕ) :
    Representation R (Matrix n n R) (homogeneousSubmodule n R m) where
  toFun := homogeneousMap m
  map_one' := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change substitution (1 : Matrix n n R) p = p
    simp
  map_mul' A B := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change substitution (A * B) p = substitution A (substitution B p)
    rw [substitution_mul]
    rfl

omit [DecidableEq n] in
/-- Evaluation of the substituted variables is the transpose matrix action. -/
theorem eval_variableImage (A : Matrix n n R) (x : n → R) (i : n) :
    eval x (variableImage A i) = (A.transpose *ᵥ x) i := by
  simp [variableImage, Matrix.mulVec, dotProduct]

omit [DecidableEq n] in
/-- The substitution has its expected evaluation formula on every polynomial. -/
theorem eval_substitution (A : Matrix n n R) (x : n → R) (p : MvPolynomial n R) :
    eval x (substitution A p) = eval (A.transpose *ᵥ x) p := by
  change aeval x (aeval (variableImage A) p) = aeval (A.transpose *ᵥ x) p
  rw [comp_aeval_apply]
  have hx : (fun i => aeval x (variableImage A i)) = A.transpose *ᵥ x :=
    funext (fun i => eval_variableImage A x i)
  rw [hx]

section SpecialLinear

variable {S : Type v} [CommRing S]

/-- Restriction of the actual matrix representation to the actual special linear group. -/
def specialLinearRepresentation (m : ℕ) :
    Representation S (Matrix.SpecialLinearGroup n S) (homogeneousSubmodule n S m) :=
  (matrixRepresentation m).comp Matrix.SpecialLinearGroup.coeMonoidHom

@[simp]
theorem specialLinearRepresentation_coe (m : ℕ) (g : Matrix.SpecialLinearGroup n S)
    (p : homogeneousSubmodule n S m) :
    (specialLinearRepresentation m g p : MvPolynomial n S) =
      substitution (g : Matrix n n S) p :=
  rfl

end SpecialLinear

end Langlands.GroupScheme.HomogeneousPolynomial
