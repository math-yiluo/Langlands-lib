import Langlands.Algebra.BinaryRepresentationNorm
import Langlands.Algebra.ReducedNormComparison
import Mathlib.RingTheory.MatrixAlgebra

/-! Actual binary matrix-algebra splitting charts and descended determinant norms. -/

noncomputable section

namespace Langlands.BinaryElementary.Splitting

universe uK uL uD uI uJ uB

open scoped TensorProduct

variable {K : Type uK} [Field K] {L : Type uL} [Field L] [Algebra K L]
  {D : Type uD} [Ring D] [Algebra K D]
  {I : Type uI} [Fintype I] [DecidableEq I]

/-- Scalar extension commutes with binary matrices, as an actual algebra equivalence. -/
def tensorMatrixEquiv :
    L ⊗[K] Matrix (Fin 2) (Fin 2) D ≃ₐ[K] Matrix (Fin 2) (Fin 2) (L ⊗[K] D) :=
  ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L)
      (matrixEquivTensor (Fin 2) K D)).trans
    (Algebra.TensorProduct.assoc K K K L D (Matrix (Fin 2) (Fin 2) K)).symm).trans
      (matrixEquivTensor (Fin 2) K (L ⊗[K] D)).symm

@[simp] theorem tensorMatrixEquiv_tmul (l : L) (M : Matrix (Fin 2) (Fin 2) D) :
    tensorMatrixEquiv (l ⊗ₜ[K] M) = fun i j => l ⊗ₜ[K] M i j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tensorMatrixEquiv, matrixEquivTensor_apply, TensorProduct.tmul_add,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.single]

/-- Flatten an actual binary block matrix, keeping the two blocks indexed by a sum. -/
def blockEquiv : Matrix (Fin 2) (Fin 2) (Matrix I I L) ≃ₐ[L]
    Matrix (I ⊕ I) (I ⊕ I) L where
  toFun := Representation.blockMap (RingHom.id _)
  invFun M := !![M.toBlocks₁₁, M.toBlocks₁₂; M.toBlocks₂₁, M.toBlocks₂₂]
  left_inv M := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  right_inv M := Matrix.fromBlocks_toBlocks M
  map_mul' M N := map_mul (Representation.blockMap (RingHom.id _)) M N
  map_add' M N := map_add (Representation.blockMap (RingHom.id _)) M N
  commutes' l := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Representation.blockMap, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]

/-- The coefficient representation induced by a genuine splitting chart. -/
def coefficientRepresentation (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) :
    D →+* Matrix I I L :=
  e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

@[simp] theorem coefficientRepresentation_apply
    (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) (a : D) :
    coefficientRepresentation e a = e (1 ⊗ₜ[K] a) := rfl

private def chartAux (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) :
    L ⊗[K] Matrix (Fin 2) (Fin 2) D ≃ₐ[K] Matrix (I ⊕ I) (I ⊕ I) L :=
  tensorMatrixEquiv.trans
    ((e.restrictScalars K).mapMatrix.trans (blockEquiv.restrictScalars K))

private theorem chartAux_tmul (e : L ⊗[K] D ≃ₐ[L] Matrix I I L)
    (l : L) (M : Matrix (Fin 2) (Fin 2) D) :
    chartAux e (l ⊗ₜ[K] M) = l • Representation.blockMap (coefficientRepresentation e) M := by
  have ht (a : D) : e (l ⊗ₜ[K] a) = l • e (1 ⊗ₜ[K] a) := by
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      (map_smul e l (1 ⊗ₜ[K] a))
  change blockEquiv (((e.restrictScalars K).mapMatrix)
    (tensorMatrixEquiv (l ⊗ₜ[K] M))) = _
  rw [tensorMatrixEquiv_tmul]
  change Matrix.fromBlocks (e (l ⊗ₜ[K] M 0 0)) (e (l ⊗ₜ[K] M 0 1))
    (e (l ⊗ₜ[K] M 1 0)) (e (l ⊗ₜ[K] M 1 1)) =
      l • Matrix.fromBlocks (e (1 ⊗ₜ[K] M 0 0)) (e (1 ⊗ₜ[K] M 0 1))
        (e (1 ⊗ₜ[K] M 1 0)) (e (1 ⊗ₜ[K] M 1 1))
  simp only [ht, Matrix.fromBlocks_smul]

/-- A genuine coefficient splitting chart induces a genuine binary matrix-algebra splitting chart. -/
def chart (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) :
    L ⊗[K] Matrix (Fin 2) (Fin 2) D ≃ₐ[L] Matrix (I ⊕ I) (I ⊕ I) L where
  __ := (chartAux e).toRingEquiv
  commutes' l := by
    change chartAux e (l ⊗ₜ[K] (1 : Matrix (Fin 2) (Fin 2) D)) = _
    rw [chartAux_tmul, map_one, Algebra.algebraMap_eq_smul_one]

@[simp] theorem chart_tmul (e : L ⊗[K] D ≃ₐ[L] Matrix I I L)
    (l : L) (M : Matrix (Fin 2) (Fin 2) D) :
    chart e (l ⊗ₜ[K] M) = l • Representation.blockMap (coefficientRepresentation e) M :=
  chartAux_tmul e l M

section Galois

open Langlands.ReducedNorm

variable [FiniteDimensional K L] [IsGalois K L] [Nonempty I]
  {J : Type uJ} [Fintype J] {B : Type uB} [Fintype B]

private theorem normImage (b : Module.Basis J K D)
    (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) (a : D) :
    algebraMap K L (normFromGalois b e K (1 ⊗ₜ[K] a)) = (e (1 ⊗ₜ[K] a)).det := by
  calc
    _ = normFromGalois b e L (1 ⊗ₜ[K] a) := by
      simpa only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one,
        Algebra.ofId_apply] using
        (normFromGalois_naturality b e (Algebra.ofId K L) (1 ⊗ₜ[K] a)).symm
    _ = _ := by
      rw [normFromGalois_eq_det b e L]
      simp

/-- The genuine descended coefficient norm, restricted to the original coefficient units. -/
def coefficientNorm (b : Module.Basis J K D)
    (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) : Dˣ →* Kˣ :=
  (normFromGaloisUnits b e K).comp
    (Units.map Algebra.TensorProduct.includeRight.toMonoidHom)

/-- The genuine descended binary matrix-algebra norm, restricted to original binary units. -/
def binaryNorm (b : Module.Basis B K (Matrix (Fin 2) (Fin 2) D))
    (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) : GL₂ D →* Kˣ :=
  (normFromGaloisUnits b (chart e) K).comp
    (Units.map Algebra.TensorProduct.includeRight.toMonoidHom)

/-- Extending coefficient norms to the splitting field recovers the actual matrix determinant. -/
theorem coefficientNorm_baseChange (b : Module.Basis J K D)
    (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) (a : Dˣ) :
    Units.map (algebraMap K L).toMonoidHom (coefficientNorm b e a) =
      Representation.coefficientNorm (coefficientRepresentation e) a := by
  apply Units.ext
  exact normImage b e (a : D)

/-- Extending binary norms recovers the determinant of the actual represented block matrix. -/
theorem binaryNorm_baseChange (b : Module.Basis B K (Matrix (Fin 2) (Fin 2) D))
    (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) (g : GL₂ D) :
    Units.map (algebraMap K L).toMonoidHom (binaryNorm b e g) =
      Representation.binaryNorm (coefficientRepresentation e) g := by
  apply Units.ext
  change algebraMap K L
      (normFromGalois b (chart e) K (1 ⊗ₜ[K] g.val)) =
    (Representation.blockMap (coefficientRepresentation e) g.val).det
  rw [normImage b (chart e) g.val, chart_tmul, one_smul]

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem ker_eq_of_baseChange {G : Type*} [Group G]
    (m : G →* Kˣ) (n : G →* Lˣ)
    (h : ∀ g, Units.map (algebraMap K L).toMonoidHom (m g) = n g) :
    m.ker = n.ker := by
  ext g
  change m g = 1 ↔ n g = 1
  rw [← h g, map_eq_one_iff _
    (Units.map_injective (FaithfulSMul.algebraMap_injective K L))]

theorem ker_coefficientNorm (b : Module.Basis J K D)
    (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) :
    (coefficientNorm b e).ker =
      (Representation.coefficientNorm (coefficientRepresentation e)).ker :=
  ker_eq_of_baseChange _ _ (coefficientNorm_baseChange b e)

theorem ker_binaryNorm (b : Module.Basis B K (Matrix (Fin 2) (Fin 2) D))
    (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) :
    (binaryNorm b e).ker =
      (Representation.binaryNorm (coefficientRepresentation e)).ker :=
  ker_eq_of_baseChange _ _ (binaryNorm_baseChange b e)

section DivisionRing

variable {D : Type uD} [DivisionRing D] [Algebra K D]

/-- Generation for the actual descended binary norm is equivalent to coefficient commutator vanishing. -/
theorem elementary_eq_ker_iff (b : Module.Basis J K D)
    (c : Module.Basis B K (Matrix (Fin 2) (Fin 2) D))
    (e : L ⊗[K] D ≃ₐ[L] Matrix I I L) :
    elementary D = (binaryNorm c e).ker ↔
      (coefficientNorm b e).ker = commutator Dˣ := by
  rw [ker_binaryNorm, ker_coefficientNorm]
  exact Representation.elementary_eq_ker_iff (coefficientRepresentation e)

end DivisionRing

end Galois

end Langlands.BinaryElementary.Splitting
