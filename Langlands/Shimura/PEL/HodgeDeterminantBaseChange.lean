import Langlands.Shimura.PEL.HodgeDeterminant
import Mathlib.RingTheory.TensorProduct.Free

/-! # Determinant polynomials over arbitrary commutative coefficient rings -/

noncomputable section

universe u v w t s r

open MvPolynomial
open scoped TensorProduct

namespace Langlands.Shimura.HodgeDeterminant

variable {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {ι : Type w} [Fintype ι]
    {κ : Type t} [Fintype κ] [DecidableEq κ]

/-- A scalar-sum form of the universal matrix. -/
theorem matrix_eq_sum (b : Module.Basis κ R M) (f : ι → Module.End R M) :
    matrix b f = ∑ i, (X i : MvPolynomial ι R) • (LinearMap.toMatrix b b (f i)).map C := by
  apply Matrix.ext
  intro j k
  simp [matrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

/-- Change of basis acts by the constant transition matrices. -/
theorem matrix_changeBasis {κ' : Type s} [Fintype κ'] [DecidableEq κ']
    (b : Module.Basis κ R M) (b' : Module.Basis κ' R M)
    (f : ι → Module.End R M) :
    (b'.toMatrix b).map C * matrix b f * (b.toMatrix b').map C = matrix b' f := by
  simp only [matrix_eq_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, ← Matrix.map_mul,
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]

/-- Polynomial basis independence, including finite rings and rings with nilpotents. -/
theorem polynomial_basis_independent_commRing
    {κ' : Type s} [Fintype κ'] [DecidableEq κ']
    (b : Module.Basis κ R M) (b' : Module.Basis κ' R M)
    (f : ι → Module.End R M) :
    polynomial b f = polynomial b' f := by
  unfold polynomial
  rw [← matrix_changeBasis b b' f, Matrix.det_conj_of_mul_eq_one]
  · simp only [← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip]
    exact Matrix.map_one _ (map_zero C) (map_one C)
  · simp only [← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip]
    exact Matrix.map_one _ (map_zero C) (map_one C)

/-- The determinant polynomial after an arbitrary coefficient-ring homomorphism. -/
def mappedPolynomial {S : Type s} [CommRing S] (g : R →+* S)
    (b : Module.Basis κ R M) (f : ι → Module.End R M) : MvPolynomial ι S :=
  MvPolynomial.map g (polynomial b f)

theorem mappedPolynomial_basis_independent {S : Type s} [CommRing S]
    (g : R →+* S) {κ' : Type r} [Fintype κ'] [DecidableEq κ']
    (b : Module.Basis κ R M) (b' : Module.Basis κ' R M)
    (f : ι → Module.End R M) :
    mappedPolynomial g b f = mappedPolynomial g b' f := by
  rw [mappedPolynomial, mappedPolynomial, polynomial_basis_independent_commRing b b']

/-- Coefficient change is compatible with the actual scalar-extended endomorphisms. -/
theorem mappedPolynomial_eq_baseChange {S : Type s} [CommRing S] [Algebra R S]
    (b : Module.Basis κ R M) (f : ι → Module.End R M) :
    mappedPolynomial (algebraMap R S) b f =
      polynomial (Algebra.TensorProduct.basis S b) (fun i => (f i).baseChange S) := by
  unfold mappedPolynomial polynomial
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro j k
  simp [matrix, LinearMap.toMatrix_baseChange]

/-- Any finite basis on the actual tensor extension computes the mapped polynomial. -/
theorem mappedPolynomial_eq_baseChange_basis
    {S : Type s} [CommRing S] [Algebra R S]
    {κ' : Type r} [Fintype κ'] [DecidableEq κ']
    (b : Module.Basis κ R M)
    (b' : Module.Basis κ' S (S ⊗[R] M))
    (f : ι → Module.End R M) :
    mappedPolynomial (algebraMap R S) b f =
      polynomial b' (fun i => (f i).baseChange S) := by
  rw [mappedPolynomial_eq_baseChange,
    polynomial_basis_independent_commRing (Algebra.TensorProduct.basis S b) b']

@[simp]
theorem coeff_mappedPolynomial {S : Type s} [CommRing S] (g : R →+* S)
    (b : Module.Basis κ R M) (f : ι → Module.End R M) (d : ι →₀ ℕ) :
    (mappedPolynomial g b f).coeff d = g ((polynomial b f).coeff d) := by
  simp only [mappedPolynomial, MvPolynomial.coeff_map]

@[simp]
theorem mappedPolynomial_id (b : Module.Basis κ R M) (f : ι → Module.End R M) :
    mappedPolynomial (RingHom.id R) b f = polynomial b f := by
  simp only [mappedPolynomial, MvPolynomial.map_id]

/-- Two successive coefficient changes compose in the same order as ring maps. -/
theorem map_mappedPolynomial {S : Type s} [CommRing S]
    {T : Type r} [CommRing T] (g : R →+* S) (h : S →+* T)
    (b : Module.Basis κ R M) (f : ι → Module.End R M) :
    MvPolynomial.map h (mappedPolynomial g b f) = mappedPolynomial (h.comp g) b f := by
  exact MvPolynomial.map_map g h (polynomial b f)

theorem mappedPolynomial_isHomogeneous {S : Type s} [CommRing S] (g : R →+* S)
    (b : Module.Basis κ R M) (f : ι → Module.End R M) :
    (mappedPolynomial g b f).IsHomogeneous (Fintype.card κ) :=
  (polynomial_isHomogeneous b f).map g

/-- Evaluation is the intrinsic determinant on the actual scalar extension. -/
theorem eval_mappedPolynomial_baseChange {S : Type s} [CommRing S] [Algebra R S]
    (b : Module.Basis κ R M) (f : ι → Module.End R M) (x : ι → S) :
    eval x (mappedPolynomial (algebraMap R S) b f) =
      LinearMap.det (∑ i, x i • (f i).baseChange S) := by
  rw [mappedPolynomial_eq_baseChange, eval_polynomial]

end Langlands.Shimura.HodgeDeterminant
