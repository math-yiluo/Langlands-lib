import Langlands.GroupScheme.Reductive.SelfDualTensorConjugation
import Langlands.GroupScheme.Reductive.ConjugationSchur
import Langlands.GroupScheme.Rational.SubquotientSpectralIntegrality

/-! # Conjugation maps from fixed tensors with an irreducible first factor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix Kronecker CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m r : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype r] [DecidableEq r]

/-- Row-first tensor coordinates of a rectangular matrix. -/
def tensorVector (M : Matrix n m k) : n × m → k := fun p => M p.1 p.2

/-- The identity matrix is an actual self-intertwiner. -/
theorem intertwines_one (σ : MatrixRepresentation G n) :
    Intertwines σ σ (1 : Matrix n n k) := by
  intro A g
  simp

/-- An all-test fixed tensor is an actual intertwiner from the dual of the second
factor to the first factor. -/
theorem intertwines_dual_of_isFixedVector_tensor {σ : MatrixRepresentation G n}
    {π : MatrixRepresentation G m} {M : Matrix n m k}
    (hM : (σ.tensor π).IsFixedVector (tensorVector M)) :
    Intertwines π.dual σ M := by
  intro S x
  have h := hM.affine S x
  have hfix : (σ.affineMatrix S x : Matrix n n S) * M.map (algebraMap k S) *
      (π.affineMatrix S x : Matrix m m S)ᵀ = M.map (algebraMap k S) := by
    ext i j
    have hij := congrFun h (i, j)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, tensorVector] at hij
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Finset.sum_mul]
    rw [← hij, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [tensor_affineMatrix_entry]
      ring
  rw [dual_affineMatrix, GeneralLinear.matrixContragredient_coe]
  calc M.map (algebraMap k S) * ((π.affineMatrix S x)⁻¹ : GL m S).valᵀ
      = (σ.affineMatrix S x : Matrix n n S) * M.map (algebraMap k S) *
          ((π.affineMatrix S x : Matrix m m S)ᵀ *
            ((π.affineMatrix S x)⁻¹ : GL m S).valᵀ) := by
        rw [← Matrix.mul_assoc, hfix]
    _ = (σ.affineMatrix S x : Matrix n n S) * M.map (algebraMap k S) := by
        rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.mul_one]

/-- Transposition dualizes an actual intertwiner. -/
theorem Intertwines.dual {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
    {C : Matrix m n k} (hC : Intertwines ρ σ C) : Intertwines σ.dual ρ.dual Cᵀ := by
  intro S x
  have h := hC S x
  rw [dual_affineMatrix, dual_affineMatrix, GeneralLinear.matrixContragredient_coe,
    GeneralLinear.matrixContragredient_coe, Matrix.transpose_map, ← Matrix.transpose_mul,
    ← Matrix.transpose_mul]
  congr 1
  calc ((σ.affineMatrix S x)⁻¹ : GL m S).val * C.map (algebraMap k S)
      = ((σ.affineMatrix S x)⁻¹ : GL m S).val * C.map (algebraMap k S) *
          ((ρ.affineMatrix S x : Matrix n n S) * ((ρ.affineMatrix S x)⁻¹ : GL n S).val) := by
        rw [Units.mul_inv, Matrix.mul_one]
    _ = ((σ.affineMatrix S x)⁻¹ : GL m S).val * (σ.affineMatrix S x : Matrix m m S) *
          C.map (algebraMap k S) * ((ρ.affineMatrix S x)⁻¹ : GL n S).val := by
        rw [← Matrix.mul_assoc, Matrix.mul_assoc _ (C.map _), h]
        simp only [Matrix.mul_assoc]
    _ = C.map (algebraMap k S) * ((ρ.affineMatrix S x)⁻¹ : GL n S).val := by
        rw [Units.inv_mul, Matrix.one_mul]

/-- A two-sided inverse of an actual intertwiner is an actual intertwiner. -/
theorem Intertwines.of_mul_eq_one {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k} {N : Matrix n m k}
    (hC : Intertwines ρ σ C) (hNC : N * C = 1) (hCN : C * N = 1) :
    Intertwines σ ρ N := by
  intro S x
  have h := hC S x
  have hNC' : N.map (algebraMap k S) * C.map (algebraMap k S) = 1 := by
    rw [← Matrix.map_mul, hNC]
    simp
  have hCN' : C.map (algebraMap k S) * N.map (algebraMap k S) = 1 := by
    rw [← Matrix.map_mul, hCN]
    simp
  calc N.map (algebraMap k S) * (σ.affineMatrix S x : Matrix m m S)
      = N.map (algebraMap k S) * (σ.affineMatrix S x : Matrix m m S) *
          (C.map (algebraMap k S) * N.map (algebraMap k S)) := by
        rw [hCN', Matrix.mul_one]
    _ = N.map (algebraMap k S) * C.map (algebraMap k S) *
          (ρ.affineMatrix S x : Matrix n n S) * N.map (algebraMap k S) := by
        rw [← Matrix.mul_assoc, Matrix.mul_assoc _ _ (C.map _), ← h]
        simp only [Matrix.mul_assoc]
    _ = (ρ.affineMatrix S x : Matrix n n S) * N.map (algebraMap k S) := by
        rw [hNC', Matrix.one_mul]

/-- A nonzero actual intertwiner into an irreducible representation of the same
coordinate size is invertible. -/
theorem isUnit_of_intertwines_of_isIrreducible {π σ : MatrixRepresentation G m}
    (hσ : σ.rationalRepresentation.IsIrreducible) {M : Matrix m m k}
    (hM : Intertwines π σ M) (hM0 : M ≠ 0) : IsUnit M := by
  let := hσ
  let F : Representation.IntertwiningMap π.rationalRepresentation
      σ.rationalRepresentation :=
    (Matrix.toLin' M).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      change M *ᵥ ((π.rationalMatrix g : Matrix m m k) *ᵥ v) =
        (σ.rationalMatrix g : Matrix m m k) *ᵥ (M *ᵥ v)
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM.rationalMatrix g])
  rcases Representation.IsIrreducible.surjective_or_eq_zero F with hs | h0
  · exact Matrix.mulVec_surjective_iff_isUnit.mp hs
  · exfalso
    apply hM0
    have h := congrArg Representation.IntertwiningMap.toLinearMap h0
    change Matrix.toLin' M = 0 at h
    exact Matrix.toLin'.injective (by rw [h, map_zero])

namespace ConjugationLinearMap

variable [IsAffine G.X.left] {ρ : MatrixRepresentation G r}
  {σ π : MatrixRepresentation G m}

/-- A tensor intertwiner and an actual identification of the second factor with the
dual of the first give a conjugation map on every scheme test. -/
def ofTensorDualIntertwiner {C : Matrix (m × m) r k}
    (hC : Intertwines ρ (σ.tensor π) C) {D : Matrix m m k}
    (hD : Intertwines π σ.dual D) : ConjugationLinearMap ρ σ :=
  ofTensorIntertwiner (hC.comp ((intertwines_one σ).tensor hD))

/-- Entries of the constructed matrix contract the tensor image with the second
coordinate change. -/
theorem ofTensorDualIntertwiner_eval {C : Matrix (m × m) r k}
    (hC : Intertwines ρ (σ.tensor π) C) {D : Matrix m m k}
    (hD : Intertwines π σ.dual D) (v : r → k) (i j : m) :
    MatrixLinear.eval (ofTensorDualIntertwiner hC hD).coeff (RingHom.id k) v i j =
      ∑ b, D j b * (C *ᵥ v) (i, b) := by
  change ((((1 : Matrix m m k) ⊗ₖ D) * C) *ᵥ v) (i, j) = _
  rw [← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single i (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
  simp

/-- A fixed vector whose tensor image is nonzero has the identity matrix as image
under an actual conjugation map, when the first tensor factor is irreducible. -/
theorem exists_eval_eq_one_of_tensor
    (hσ : σ.rationalRepresentation.IsIrreducible) {C : Matrix (m × m) r k}
    (hC : Intertwines ρ (σ.tensor π) C) (v : r → k) (hv : ρ.IsFixedVector v)
    (hne : C *ᵥ v ≠ 0) :
    ∃ φ : ConjugationLinearMap ρ σ,
      MatrixLinear.eval φ.coeff (RingHom.id k) v = 1 := by
  let M : Matrix m m k := Matrix.of fun i j => (C *ᵥ v) (i, j)
  have hMv : tensorVector M = C *ᵥ v := rfl
  have hfix : (σ.tensor π).IsFixedVector (tensorVector M) := by
    rw [hMv]
    exact hC.isFixedVector hv
  have hM : Intertwines π.dual σ M := intertwines_dual_of_isFixedVector_tensor hfix
  have hM0 : M ≠ 0 := by
    intro h0
    apply hne
    rw [← hMv, h0]
    rfl
  have hunit : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).mp (isUnit_of_intertwines_of_isIrreducible hσ hM hM0)
  have hMt : Intertwines σ.dual π Mᵀ := by
    have h := hM.dual
    rwa [dual_dual] at h
  have hunitT : IsUnit Mᵀ.det := by
    rwa [Matrix.det_transpose]
  have hD : Intertwines π σ.dual (Mᵀ)⁻¹ :=
    hMt.of_mul_eq_one (Matrix.nonsing_inv_mul _ hunitT) (Matrix.mul_nonsing_inv _ hunitT)
  refine ⟨ofTensorDualIntertwiner hC hD, ?_⟩
  ext i j
  rw [ofTensorDualIntertwiner_eval]
  have hij := congrFun (congrFun (Matrix.mul_nonsing_inv M hunit) i) j
  rw [Matrix.mul_apply] at hij
  rw [← hij, ← Matrix.transpose_nonsing_inv]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

end ConjugationLinearMap
end Langlands.GroupScheme.MatrixRepresentation
