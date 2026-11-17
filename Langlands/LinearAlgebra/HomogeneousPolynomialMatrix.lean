import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Matrices of homogeneous polynomial substitution -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v w

namespace Langlands.LinearAlgebra.HomogeneousPolynomial

open MvPolynomial

variable (σ : Type w) (d : ℕ)

/-- The exponent vectors of monomials of a specified total degree. -/
abbrev MonomialIndex := {e : σ →₀ ℕ // e.degree = d}

instance [Finite σ] : Finite (MonomialIndex σ d) :=
  (Finsupp.finite_of_degree_eq d).to_subtype

noncomputable instance [Finite σ] : Fintype (MonomialIndex σ d) :=
  Fintype.ofFinite _

variable (R : Type u) [CommRing R]

/-- The monomial basis of a homogeneous polynomial submodule. -/
def monomialBasis : Module.Basis (MonomialIndex σ d) R (homogeneousSubmodule σ R d) :=
  (basisRestrictSupport R {e : σ →₀ ℕ | e.degree = d}).map
    (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported σ R d).symm)

@[simp]
theorem monomialBasis_repr (p : homogeneousSubmodule σ R d) (e : MonomialIndex σ d) :
    (monomialBasis σ d R).repr p e = p.val.coeff e.val := by
  rfl

@[simp]
theorem monomialBasis_val (e : MonomialIndex σ d) :
    ((monomialBasis σ d R) e).val = monomial e.val (1 : R) := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  change ((Finsupp.supportedEquivFinsupp (R := R)
    {e : σ →₀ ℕ | e.degree = d}).symm (Finsupp.single e (1 : R)) : (σ →₀ ℕ) →₀ R) =
    Finsupp.single e.val (1 : R)
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

variable {σ d R}

section Substitution

variable [Fintype σ] [DecidableEq σ]

/-- The linear polynomial given by one column of a matrix. -/
def column (M : Matrix σ σ R) (j : σ) : MvPolynomial σ R :=
  ∑ i, C (M i j) * X i

omit [DecidableEq σ] in
theorem column_isHomogeneous (M : Matrix σ σ R) (j : σ) :
    (column M j).IsHomogeneous 1 := by
  apply Submodule.sum_mem (homogeneousSubmodule σ R 1)
  intro i _
  exact isHomogeneous_C_mul_X (M i j) i

@[simp]
theorem column_diagonal (a : σ → R) (j : σ) :
    column (Matrix.diagonal a) j = C (a j) * X j := by
  classical
  simp [column, Matrix.diagonal_apply, apply_ite, ite_mul]

@[simp]
theorem column_one (j : σ) : column (1 : Matrix σ σ R) j = X j := by
  simpa only [Matrix.diagonal_one, map_one, one_mul] using
    column_diagonal (fun _ : σ => (1 : R)) j

omit [DecidableEq σ] in
theorem column_mul (M N : Matrix σ σ R) (j : σ) :
    column (M * N) j = aeval (column M) (column N j) := by
  simp only [column, Matrix.mul_apply, map_sum, map_mul, aeval_C, aeval_X,
    algebraMap_eq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The action of a matrix by linear substitution on homogeneous polynomials. -/
def action (M : Matrix σ σ R) (d : ℕ) :
    homogeneousSubmodule σ R d →ₗ[R] homogeneousSubmodule σ R d :=
  (((aeval (column M)).toLinearMap).comp
    (homogeneousSubmodule σ R d).subtype).codRestrict _ (fun p => by
      change (aeval (column M) p.val).IsHomogeneous d
      simpa only [one_mul] using p.property.aeval (column M) (column_isHomogeneous M))

omit [DecidableEq σ] in
@[simp]
theorem action_val (M : Matrix σ σ R) (d : ℕ) (p : homogeneousSubmodule σ R d) :
    (action M d p).val = aeval (column M) p.val := rfl

@[simp]
theorem action_one (d : ℕ) : action (1 : Matrix σ σ R) d = LinearMap.id := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change aeval (column (1 : Matrix σ σ R)) p.val = p.val
  rw [show column (1 : Matrix σ σ R) = X from funext column_one]
  exact aeval_X_left_apply p.val

omit [DecidableEq σ] in
theorem action_mul (M N : Matrix σ σ R) (d : ℕ) :
    action (M * N) d = (action M d).comp (action N d) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change aeval (column (M * N)) p.val =
    aeval (column M) (aeval (column N) p.val)
  rw [comp_aeval_apply]
  rw [show column (M * N) = (fun j => aeval (column M) (column N j)) from
    funext (column_mul M N)]

/-- The matrix of homogeneous substitution in the actual monomial basis. -/
def representation (M : Matrix σ σ R) (d : ℕ) :
    Matrix (MonomialIndex σ d) (MonomialIndex σ d) R :=
  LinearMap.toMatrix (monomialBasis σ d R) (monomialBasis σ d R) (action M d)

theorem representation_apply (M : Matrix σ σ R) (d : ℕ)
    (e f : MonomialIndex σ d) :
    representation M d e f = (aeval (column M) (monomial f.val (1 : R))).coeff e.val := by
  rw [representation, LinearMap.toMatrix_apply, monomialBasis_repr, action_val,
    monomialBasis_val]

@[simp]
theorem representation_one (d : ℕ) :
    representation (1 : Matrix σ σ R) d = 1 := by
  classical
  rw [representation, action_one, LinearMap.toMatrix_id]

theorem representation_mul (M N : Matrix σ σ R) (d : ℕ) :
    representation (M * N) d = representation M d * representation N d := by
  classical
  rw [representation, action_mul, LinearMap.toMatrix_comp (monomialBasis σ d R)
    (monomialBasis σ d R) (monomialBasis σ d R)]
  rfl

theorem aeval_diagonal_monomial (a : σ → R) (e : σ →₀ ℕ) :
    aeval (column (Matrix.diagonal a)) (monomial e (1 : R)) =
      monomial e (e.prod (fun i k => a i ^ k)) := by
  classical
  rw [aeval_monomial]
  simp only [map_one, one_mul, column_diagonal, mul_pow, Finsupp.prod,
    Finset.prod_mul_distrib]
  simp only [← map_pow, ← map_prod]
  rw [prod_X_pow_eq_monomial, C_mul_monomial, mul_one]

theorem representation_diagonal (a : σ → R) (d : ℕ) :
    representation (Matrix.diagonal a) d =
      Matrix.diagonal (fun e : MonomialIndex σ d => e.val.prod (fun i k => a i ^ k)) := by
  classical
  ext e f
  rw [representation_apply, aeval_diagonal_monomial, coeff_monomial]
  by_cases h : e = f
  · subst f
    simp
  · have h' : e.val ≠ f.val := fun hval => h (Subtype.ext hval)
    simp [h, Ne.symm h']

theorem det_representation_diagonal (a : σ → R) (d : ℕ) :
    (representation (Matrix.diagonal a) d).det =
      ∏ e : MonomialIndex σ d, e.val.prod (fun i k => a i ^ k) := by
  rw [representation_diagonal, Matrix.det_diagonal]

section Map

variable {S : Type v} [CommRing S] (f : R →+* S)

omit [DecidableEq σ] in
theorem map_column (M : Matrix σ σ R) (j : σ) :
    MvPolynomial.map f (column M j) = column (M.map f) j := by
  simp [column]

omit [DecidableEq σ] in
theorem map_aeval_monomial (M : Matrix σ σ R) (e : σ →₀ ℕ) :
    MvPolynomial.map f (aeval (column M) (monomial e (1 : R))) =
      aeval (column (M.map f)) (monomial e (1 : S)) := by
  simp only [aeval_monomial, map_one, one_mul, Finsupp.prod, map_prod, map_pow,
    map_column]

/-- Homogeneous substitution matrices commute with every homomorphism of coefficient rings. -/
theorem representation_map (M : Matrix σ σ R) (d : ℕ) :
    (representation M d).map f = representation (M.map f) d := by
  ext e g
  rw [Matrix.map_apply, representation_apply, representation_apply, ← coeff_map]
  rw [map_aeval_monomial f M g.val]

end Map

end Substitution

end Langlands.LinearAlgebra.HomogeneousPolynomial
