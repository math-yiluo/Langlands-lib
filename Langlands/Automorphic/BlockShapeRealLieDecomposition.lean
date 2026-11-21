import Langlands.Automorphic.BlockShapeLeviSliceDifferential
import Langlands.Global.ArchimedeanCompactLieAlgebra
import Langlands.Group.GL.BlockLieDecomposition
import Langlands.Representation.Geometric.WeylDefinitions

/-! Decomposition of real archimedean Lie directions for a block parabolic. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Automorphic

open Langlands.GeneralLinear Langlands.Geometric Langlands.Global Langlands.Global.ArchimedeanGL NumberField
open scoped Classical Matrix.Norms.Operator TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] {n : ℕ} (B : BlockShape n)

/-- The real Lie directions with entries only in strictly upper blocks. -/
def IsStrictUpperBlockLie (X : RealLieAlgebra F n) : Prop :=
  ∀ a b, blockIndex B b ≤ blockIndex B a → realLieAlgebraToMatrix F n X a b = 0

variable [NumberField F]

omit [NumberField F] in
private theorem sum_archimedeanBlockMatrixInclusion
    (D : ∀ i, ArchimedeanMatrix F (B.size i)) :
    (∑ i, archimedeanBlockMatrixInclusion F B i (D i)) =
      Matrix.reindex B.indexEquiv B.indexEquiv (Matrix.blockDiagonal' D) := by
  let A : (∀ j, ArchimedeanMatrix F (B.size j)) →ₗ[ℝ] ArchimedeanMatrix F n :=
    (Matrix.reindexLinearEquiv ℝ (mixedEmbedding.mixedSpace F) B.indexEquiv B.indexEquiv).toLinearMap.comp
      ({ toFun := Matrix.blockDiagonal'
         map_add' := Matrix.blockDiagonal'_add
         map_smul' := Matrix.blockDiagonal'_smul } :
        (∀ j, ArchimedeanMatrix F (B.size j)) →ₗ[ℝ]
          Matrix B.Index B.Index (mixedEmbedding.mixedSpace F))
  change (∑ i, A (Pi.single i (D i))) = A D
  rw [← map_sum, Finset.univ_sum_single]

omit [NumberField F] in
/-- Actual real Lie directions split into block Lie directions, a radical
direction, and a standard compact direction. -/
theorem exists_realLie_block_upper_compact (X : RealLieAlgebra F n) :
    ∃ (D : ∀ i, RealLieAlgebra F (B.size i)) (U : RealLieAlgebra F n)
      (C : compactLieSubalgebra F n),
      IsStrictUpperBlockLie F B U ∧
      X = (∑ i, blockShapeRealLieInclusion F B i (D i)) + U + C.val := by
  let e := realLieAlgebraToMatrix F n
  obtain ⟨D, U, C, hC, hU, hX⟩ := B.exists_blockDiagonal_strictUpper_skew (e X)
  let D' (i : Fin B.length) := (realLieAlgebraToMatrix F (B.size i)).symm (D i)
  let C' : compactLieSubalgebra F n :=
    ⟨e.symm C, (mem_compactLieSubalgebra F n _).mpr hC⟩
  refine ⟨D', e.symm U, C', ?_, ?_⟩
  · intro a b h
    change e (e.symm U) a b = 0
    rw [e.apply_symm_apply]
    exact hU a b h
  · apply e.injective
    rw [map_add, map_add, map_sum]
    have hd (i : Fin B.length) :
        e (blockShapeRealLieInclusion F B i (D' i)) =
          archimedeanBlockMatrixInclusion F B i (D i) := by
      rw [show e = realLieAlgebraToMatrix F n from rfl, blockShapeRealLieInclusion_matrix]
      change archimedeanBlockMatrixInclusion F B i
        ((realLieAlgebraToMatrix F (B.size i)) ((realLieAlgebraToMatrix F (B.size i)).symm (D i))) = _
      rw [LinearEquiv.apply_symm_apply]
    rw [show e C'.val = C from e.apply_symm_apply C, e.apply_symm_apply]
    simp only [hd]
    rw [sum_archimedeanBlockMatrixInclusion]
    exact hX

end Langlands.Automorphic
