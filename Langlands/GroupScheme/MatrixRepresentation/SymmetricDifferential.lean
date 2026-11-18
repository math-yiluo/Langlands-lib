import Langlands.GroupScheme.MatrixRepresentation.SymmetricPower
import Langlands.GroupScheme.Lie.RepresentationDifferential
import Mathlib.Algebra.MvPolynomial.Derivation

/-! # Differentiating actual symmetric-power matrices -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.Algebra.SymmetricMatrix

namespace SymmetricDifferential

variable (R : Type u) [CommRing R] (n : Type)

/-- Interchange the polynomial variables with the dual-number coefficients. -/
def dualPolynomialMap : MvPolynomial n (DualNumber R) →+* DualNumber (MvPolynomial n R) :=
  MvPolynomial.eval₂Hom
    (GeneralLinear.DualNumber.coefficientMap (MvPolynomial.C : R →+* MvPolynomial n R))
    (fun j => TrivSqZeroExt.inl (MvPolynomial.X j))

@[simp]
theorem dualPolynomialMap_C (z : DualNumber R) :
    dualPolynomialMap R n (MvPolynomial.C z) =
      ⟨MvPolynomial.C z.fst, MvPolynomial.C z.snd⟩ := by
  simp [dualPolynomialMap, GeneralLinear.DualNumber.coefficientMap]
  rfl

@[simp]
theorem dualPolynomialMap_X (j : n) :
    dualPolynomialMap R n (MvPolynomial.X j) = TrivSqZeroExt.inl (MvPolynomial.X j) := by
  simp [dualPolynomialMap]

/-- Epsilon coefficients can be extracted before or after polynomial
coefficients. -/
theorem dualPolynomialMap_snd_coeff (P : MvPolynomial n (DualNumber R)) (a : n →₀ ℕ) :
    (dualPolynomialMap R n P).snd.coeff a = (P.coeff a).snd := by
  classical
  induction P using MvPolynomial.induction_on generalizing a with
  | C z =>
    simp only [dualPolynomialMap_C, TrivSqZeroExt.snd_mk, MvPolynomial.coeff_C]
    split_ifs <;> rfl
  | add P Q hP hQ =>
    simp only [map_add, TrivSqZeroExt.snd_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
  | mul_X P j hP =>
    simp only [map_mul, dualPolynomialMap_X, TrivSqZeroExt.snd_mul,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_eq_mul, mul_zero, zero_add]
    change ((dualPolynomialMap R n P).snd * MvPolynomial.X j).coeff a =
      ((P * MvPolynomial.X j).coeff a).snd
    erw [MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
    split_ifs <;> simp_all

/-- The algebra homomorphism associated with a derivation, recording its
value as an epsilon coefficient. -/
def derivationLift (D : Derivation R (MvPolynomial n R) (MvPolynomial n R)) :
    MvPolynomial n R →ₐ[R] DualNumber (MvPolynomial n R) where
  toFun P := ⟨P, D P⟩
  map_one' := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact D.map_one_eq_zero
  map_mul' P Q := by
    apply TrivSqZeroExt.ext
    · rfl
    · change D (P * Q) = P * D Q + D P * Q
      simpa only [smul_eq_mul, mul_comm] using D.leibniz P Q
  map_zero' := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact map_zero D
  map_add' P Q := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact map_add D P Q
  commutes' r := by
    rw [TrivSqZeroExt.algebraMap_eq_inl']
    apply TrivSqZeroExt.ext
    · rfl
    · exact MvPolynomial.derivation_C D r

@[simp]
theorem derivationLift_fst (D : Derivation R (MvPolynomial n R) (MvPolynomial n R))
    (P : MvPolynomial n R) : (derivationLift R n D P).fst = P := rfl

@[simp]
theorem derivationLift_snd (D : Derivation R (MvPolynomial n R) (MvPolynomial n R))
    (P : MvPolynomial n R) : (derivationLift R n D P).snd = D P := rfl

section Finite

variable {R n} [Fintype n] [DecidableEq n]

/-- The derivation extending the column action of a matrix on linear
polynomial generators. -/
def derivation (N : Matrix n n R) : Derivation R (MvPolynomial n R) (MvPolynomial n R) :=
  MvPolynomial.mkDerivation R (fun j => ∑ i, MvPolynomial.C (N i j) * MvPolynomial.X i)

/-- An infinitesimal matrix, with identity constant term and prescribed epsilon
coefficient. -/
def infinitesimalMatrix (N : Matrix n n R) : Matrix n n (DualNumber R) :=
  fun i j => ⟨if i = j then 1 else 0, N i j⟩

omit [DecidableEq n] in
@[simp]
theorem derivation_X (N : Matrix n n R) (j : n) :
    derivation N (MvPolynomial.X j) =
      ∑ i, MvPolynomial.C (N i j) * MvPolynomial.X i := by
  simp [derivation]

theorem dual_substitute_X (N : Matrix n n R) (j : n) :
    dualPolynomialMap R n
      (substitute (infinitesimalMatrix N) (MvPolynomial.X j)) =
        derivationLift R n (derivation N) (MvPolynomial.X j) := by
  rw [substitute_X, map_sum]
  have hC (i : n) : dualPolynomialMap R n (MvPolynomial.C (infinitesimalMatrix N i j)) =
      (⟨MvPolynomial.C (if i = j then (1 : R) else 0), MvPolynomial.C (N i j)⟩ :
        DualNumber (MvPolynomial n R)) :=
    dualPolynomialMap_C R n _
  have hprod (i : n) : dualPolynomialMap R n
      (MvPolynomial.C (infinitesimalMatrix N i j) * MvPolynomial.X i) =
        (⟨MvPolynomial.C (if i = j then (1 : R) else 0) * MvPolynomial.X i,
          MvPolynomial.C (N i j) * MvPolynomial.X i⟩ : DualNumber (MvPolynomial n R)) := by
    rw [map_mul, hC, dualPolynomialMap_X]
    apply TrivSqZeroExt.ext
    · rfl
    · change MvPolynomial.C (if i = j then (1 : R) else 0) * 0 +
          MvPolynomial.C (N i j) * MvPolynomial.X i = _
      rw [mul_zero, zero_add]
      rfl
  simp only [hprod]
  apply TrivSqZeroExt.ext
  · erw [TrivSqZeroExt.fst_sum]
    change (∑ i, MvPolynomial.C (if i = j then (1 : R) else 0) * MvPolynomial.X i) =
      MvPolynomial.X j
    simp [ite_mul]
  · erw [TrivSqZeroExt.snd_sum]
    change (∑ i, MvPolynomial.C (N i j) * MvPolynomial.X i) =
      derivation N (MvPolynomial.X j)
    rw [derivation_X]

/-- Infinitesimal symmetric substitution is exactly the derivation lift. -/
theorem dual_substitute (N : Matrix n n R) (P : MvPolynomial n R) :
    dualPolynomialMap R n
      (substitute (infinitesimalMatrix N)
        (MvPolynomial.map (TrivSqZeroExt.inlHom R R) P)) =
      derivationLift R n (derivation N) P := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    simp only [MvPolynomial.map_C, substitute_C, dualPolynomialMap_C]
    apply TrivSqZeroExt.ext
    · rfl
    · change MvPolynomial.C (0 : R) = derivation N (MvPolynomial.C r)
      rw [MvPolynomial.derivation_C, map_zero]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP => simp only [map_mul, MvPolynomial.map_X, hP, dual_substitute_X]

/-- The epsilon matrix of a symmetric power at an infinitesimal matrix. -/
def matrix (N : Matrix n n R) (d : ℕ) : Matrix (Index n d) (Index n d) R :=
  fun a b => (Langlands.Algebra.SymmetricMatrix.matrix (infinitesimalMatrix N) d a b).snd

/-- The differential matrix entries are the coefficients of the genuine
polynomial derivation. -/
theorem matrix_apply (N : Matrix n n R) (d : ℕ) (a b : Index n d) :
    matrix N d a b = (derivation N (MvPolynomial.monomial b.val 1)).coeff a.val := by
  unfold matrix
  rw [Langlands.Algebra.SymmetricMatrix.matrix_apply]
  rw [← dualPolynomialMap_snd_coeff]
  have h := congrArg (fun z : DualNumber (MvPolynomial n R) => z.snd.coeff a.val)
    (dual_substitute N (MvPolynomial.monomial b.val 1))
  simpa only [MvPolynomial.map_monomial, map_one, derivationLift_snd] using h

/-- The differential matrix acts by the actual polynomial derivation in
canonical homogeneous coordinates. -/
theorem matrix_mulVec (N : Matrix n n R) (d : ℕ)
    (P : MvPolynomial.homogeneousSubmodule n R d) :
    matrix N d *ᵥ (basis R n d).equivFun P =
      fun a => (derivation N (P : MvPolynomial n R)).coeff a.val := by
  have hsum : (P : MvPolynomial n R) =
      ∑ b : Index n d, (P : MvPolynomial n R).coeff b.val • MvPolynomial.monomial b.val 1 := by
    have h := congrArg
      (fun Q : MvPolynomial.homogeneousSubmodule n R d => (Q : MvPolynomial n R))
      ((basis R n d).sum_repr P)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, basis_repr, basis_apply] using h.symm
  funext a
  change (∑ b, matrix N d a b * (P : MvPolynomial n R).coeff b.val) = _
  conv_rhs => rw [hsum]
  simp only [map_sum, Derivation.map_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [matrix_apply, mul_comm]

end Finite

end SymmetricDifferential

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The tangent matrix of the actual symmetric representation is the genuine
symmetric derivation matrix. -/
theorem symmetricPower_tangentMatrix (ρ : MatrixRepresentation G n) (d : ℕ)
    (X : lieKernel G k) :
    (ρ.symmetricPower d).tangentMatrix k X =
      SymmetricDifferential.matrix (ρ.tangentMatrix k X) d := by
  have h := congrArg Subtype.val (ρ.pointKernelEquiv_tangentMatrix k X)
  change GeneralLinear.DualNumber.pointUnit (ρ.tangentMatrix k X) =
    X.val ≫ ρ.hom.hom at h
  have hM : ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val =
      GeneralLinear.DualNumber.matrixUnit (ρ.tangentMatrix k X) := by
    rw [affineMatrix_apply, ← h, GeneralLinear.DualNumber.pointUnit_matrix]
  ext a b
  change (((ρ.symmetricPower d).affineMatrix
    (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val).val a b).snd = _
  rw [symmetricPower_affineMatrix, hM]
  change (Langlands.Algebra.SymmetricMatrix.matrix
    (GeneralLinear.DualNumber.matrixUnit (ρ.tangentMatrix k X) : Matrix n n (DualNumber k))
      d a b).snd = _
  have hN : (GeneralLinear.DualNumber.matrixUnit (ρ.tangentMatrix k X) :
      Matrix n n (DualNumber k)) =
      SymmetricDifferential.infinitesimalMatrix (ρ.tangentMatrix k X) := by
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext
    · by_cases hij : i = j <;> simp [GeneralLinear.DualNumber.matrixUnit_val,
        GeneralLinear.DualNumber.epsilonMatrix_apply, SymmetricDifferential.infinitesimalMatrix,
        hij]
    · by_cases hij : i = j <;> simp [GeneralLinear.DualNumber.matrixUnit_val,
        GeneralLinear.DualNumber.epsilonMatrix_apply, SymmetricDifferential.infinitesimalMatrix,
        hij]
  rw [hN]
  rfl

end Langlands.GroupScheme.MatrixRepresentation
