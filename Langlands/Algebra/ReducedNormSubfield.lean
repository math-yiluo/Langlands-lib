import Langlands.Algebra.ReducedCharpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.LinearAlgebra.Dimension.Free

/-! Restriction of the actual reduced norm to a field of reduced degree. -/

noncomputable section

namespace Langlands.CentralSimple

open scoped TensorProduct
open _root_.Polynomial

universe u uL uM uI uJ

section Linear

variable {K : Type*} [Field K] {L : Type uL} [Field L] [Algebra K L]
  {M : Type uM} [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M]
  {I : Type uI} [Fintype I] [DecidableEq I]
  {J : Type uJ} [Fintype J] [DecidableEq J]

/-- The characteristic polynomial of a block diagonal matrix is the product of those of its blocks. -/
theorem charpoly_blockDiagonal (f : J → Matrix I I K) :
    (Matrix.blockDiagonal f).charpoly = ∏ j, (f j).charpoly := by
  have h : (Matrix.blockDiagonal f).charmatrix =
      Matrix.blockDiagonal (fun j => (f j).charmatrix) := by
    apply Matrix.ext
    intro ⟨i,j⟩ ⟨i',j'⟩
    by_cases hj : j = j'
    · subst j'
      simp [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal, Matrix.blockDiagonal_apply]
    · simp [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal, Matrix.blockDiagonal_apply, hj]
  simp only [Matrix.charpoly, h, Matrix.det_blockDiagonal]

/-- In a tower basis, scalar multiplication is a block diagonal family of field multiplications. -/
theorem toMatrix_restrictScalars_smul (b : Module.Basis I K L) (c : Module.Basis J L M)
    (x : L) :
    LinearMap.toMatrix (b.smulTower' c) (b.smulTower' c)
        ((x • (LinearMap.id : M →ₗ[L] M)).restrictScalars K) =
      (Matrix.blockDiagonal (fun _ : J => Algebra.leftMulMatrix b x)).reindex
        (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
  rw [LinearMap.restrictScalars_toMatrix]
  simp only [map_smul, LinearMap.toMatrix_id, Matrix.smul_one_eq_diagonal,
    Matrix.diagonal_map (map_zero _), Matrix.comp_diagonal]

/-- Restricting a scalar operator from a finite extension repeats its field characteristic polynomial. -/
theorem charpoly_restrictScalars_smul [FiniteDimensional K L] [FiniteDimensional K M]
    [FiniteDimensional L M] (x : L) :
    ((x • (LinearMap.id : M →ₗ[L] M)).restrictScalars K).charpoly =
      (Algebra.lmul K L x).charpoly ^ Module.finrank L M := by
  let b := Module.finBasis K L
  let c := Module.finBasis L M
  rw [← LinearMap.charpoly_toMatrix _ (b.smulTower' c),
    toMatrix_restrictScalars_smul, Matrix.charpoly_reindex, charpoly_blockDiagonal]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  change (LinearMap.toMatrix b b (Algebra.lmul K L x)).charpoly ^ _ = _
  rw [LinearMap.charpoly_toMatrix]

end Linear

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  {L : Type uL} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The actual canonical reduced norm restricted along a finite field embedding. -/
def reducedNormOnSubfield (ι : L →ₐ[K] A) : L →* K :=
  (reducedNorm K A K).toMonoidHom.comp
    ((Algebra.TensorProduct.includeRight : A →ₐ[K] K ⊗[K] A).comp ι).toMonoidHom

/-- On a subfield of reduced degree, reduced characteristic polynomial is field characteristic polynomial. -/
theorem reducedCharpoly_eq_field_charpoly (ι : L →ₐ[K] A)
    (hdeg : Module.finrank K L = reducedDegree K A) (a : L) :
    reducedCharpoly K A (ι a) = (Algebra.lmul K L a).charpoly := by
  let : Module L A := Module.compHom A ι.toRingHom
  let : IsScalarTower K L A := ⟨fun k l x => by
    change ι (k • l) * x = k • (ι l * x)
    rw [map_smul, smul_mul_assoc]⟩
  let : FiniteDimensional L A := Module.Finite.of_restrictScalars_finite K L A
  have hdim : Module.finrank L A = reducedDegree K A := by
    have h := Module.finrank_mul_finrank K L A
    rw [hdeg, (reducedNorm_degree_spec K A).2] at h
    exact Nat.eq_of_mul_eq_mul_left (reducedNorm_degree_spec K A).1 h
  have hm : (a • (LinearMap.id : A →ₗ[L] A)).restrictScalars K =
      Algebra.lmul K A (ι a) := by
    ext x
    rfl
  apply Langlands.Polynomial.eq_of_monic_pow_eq (reducedCharpoly_monic K A (ι a))
    (LinearMap.charpoly_monic _) (Nat.ne_of_gt (reducedNorm_degree_spec K A).1)
  rw [← charpoly_leftMulMatrix_eq_reducedCharpoly_pow K A (Module.finBasis K A)]
  change (LinearMap.toMatrix _ _ (Algebra.lmul K A (ι a))).charpoly = _
  rw [LinearMap.charpoly_toMatrix, ← hm, charpoly_restrictScalars_smul, hdim]

/-- The canonical reduced norm restricts to field norm on a field of reduced degree. -/
theorem reducedNorm_eq_field_norm (ι : L →ₐ[K] A)
    (hdeg : Module.finrank K L = reducedDegree K A) (a : L) :
    reducedNorm K A K ((1 : K) ⊗ₜ[K] ι a) = Algebra.norm K a := by
  have h := congrArg (fun p : K[X] => p.eval 0)
    (reducedCharpoly_eq_field_charpoly K A ι hdeg (-a))
  rw [reducedCharpoly_eval, LinearMap.eval_charpoly] at h
  simpa [TensorProduct.neg_tmul, TensorProduct.tmul_neg, Algebra.norm_apply] using h

/-- At reduced field degree, restriction of reduced norm is the field norm homomorphism. -/
theorem reducedNormOnSubfield_eq_norm (ι : L →ₐ[K] A)
    (hdeg : Module.finrank K L = reducedDegree K A) :
    reducedNormOnSubfield K A ι = Algebra.norm K := by
  ext a
  exact reducedNorm_eq_field_norm K A ι hdeg a

end Langlands.CentralSimple
