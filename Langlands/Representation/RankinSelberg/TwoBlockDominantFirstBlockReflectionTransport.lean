import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionMatrices
import Langlands.Representation.RankinSelberg.UnequalRankComplementaryConjugationProof

/-! # Actual reflected test arguments in the dominant first-block calculation -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
  TwoBlockLowerFirstBlockQuotient
  TwoBlockDominantRectangular.BlockAlgebra

universe uK uF uW uE

section Matrices

variable {K : Type uK} [Field K]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)

/-- The first rectangle produced by reflecting the actual smaller JPSS matrix. -/
def firstBlockReflectedRectangle {a q : ℕ} (v : GeneralLinear a K)
    (z : Matrix (Fin q) (Fin a) K) : Matrix (Fin a) (Fin q) K :=
  -(weylLong a K).val * v.val * z.transpose

/-- The two disjoint rectangles multiply without a cross term. -/
theorem firstBlock_rectangle_product
    (x : Matrix (Fin (m 0 + 1)) (Fin k) K)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K) :
    TwoBlockDominantRectangular.rectangleUnipotent h rfl x
        (0 : Matrix (Fin j) (Fin (m 1 + 1)) K) *
      TwoBlockDominantRectangular.rectangleUnipotent h rfl
        (0 : Matrix (Fin (m 0 + 1)) (Fin k) K) Y =
      TwoBlockDominantRectangular.rectangleUnipotent h rfl x Y := by
  unfold TwoBlockDominantRectangular.rectangleUnipotent
  rw [← map_mul]
  congr 1
  apply Units.ext
  simp [three_mul, TwoBlockDominantRectangular.padX,
    TwoBlockDominantRectangular.padY, Matrix.fromCols_mul_fromRows]

/-- The actual small block Weyl is fixed by inverse transpose. -/
theorem inverseTranspose_firstBlockWeylAt :
    inverseTranspose (t + (j + k + 1) + 1) K
      (blockWeylAt (m 0) (t + (j + k + 1))
        (by have := blockRanks_add h; omega)) =
      blockWeylAt (m 0) (t + (j + k + 1))
        (by have := blockRanks_add h; omega) := by
  rw [UnequalRankComplementaryConjugationProof.blockWeylAt_eq,
    inverseTranspose_permutation]

/-- The reflected smaller test has exactly the argument of the actual lower kernel. -/
theorem firstBlock_reflected_test_matrix
    (v : GeneralLinear (m 0 + 1) K)
    (z : Matrix (Fin k) (Fin (m 0 + 1)) K)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) K)
    (g : GeneralLinear (t + 1) K) :
    weylLong (t + (j + k + 1) + 1) K *
      inverseTranspose (t + (j + k + 1) + 1) K
        (GeneralLinear.reindex (finCongr (by have := blockRanks_add h; omega))
            (unequalRankMatrix k (m 1 + 1 + j)
              (weylLong (m 0 + 1) K * inverseTranspose (m 0 + 1) K v) z) *
          blockWeylAt (m 0) (t + (j + k + 1))
            (by have := blockRanks_add h; omega)) *
      (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
        appendIdentity t (j + k + 1) g) =
      TwoBlockDominantRectangular.matrix h rfl
        (firstBlockEmbedding h K v * g)
        (firstBlockReflectedRectangle v z)
        (Y.submatrix Fin.rev Fin.rev) := by
  unfold firstBlockReflectedRectangle
  rw [map_mul, inverseTranspose_firstBlockWeylAt h j k]
  rw [← mul_assoc, firstBlock_reflection_matrix h j k]
  have hY := blockWeyl_firstBlockRemaining (K := K) h j k Y
  have hY' : TwoBlockDominantRectangular.blockWeyl h rfl *
        rectangularUnipotent j k (firstBlockColumns h j 0 Y) =
      TwoBlockDominantRectangular.rectangleUnipotent h rfl
          (0 : Matrix (Fin (m 0 + 1)) (Fin k) K) (Y.submatrix Fin.rev Fin.rev) *
        TwoBlockDominantRectangular.blockWeyl h rfl := by
    rw [← hY, mul_assoc, TwoBlockDominantRectangular.blockWeyl_mul_self, mul_one]
  change _ = weylLong (t + (j + k + 1) + 1) K *
    TwoBlockDominantRectangular.rectangleUnipotent h rfl
      (-(weylLong (m 0 + 1) K).val * v.val * z.transpose)
      (Y.submatrix Fin.rev Fin.rev) *
    TwoBlockDominantRectangular.blockWeyl h rfl *
    appendIdentity t (j + k + 1) (firstBlockEmbedding h K v * g)
  rw [map_mul]
  calc
    _ = weylLong (t + (j + k + 1) + 1) K *
        ((TwoBlockDominantRectangular.rectangleUnipotent h rfl
            (-(weylLong (m 0 + 1) K).val * v.val * z.transpose) 0) *
          (TwoBlockDominantRectangular.blockWeyl h rfl *
            rectangularUnipotent j k (firstBlockColumns h j 0 Y)) *
          appendIdentity t (j + k + 1) (firstBlockEmbedding h K v) *
          appendIdentity t (j + k + 1) g) := by
      simp only [mul_assoc]
      rw [← mul_assoc (appendIdentity t (j + k + 1) (firstBlockEmbedding h K v))
        (rectangularUnipotent j k (firstBlockColumns h j 0 Y))
        (appendIdentity t (j + k + 1) g), firstBlockRemaining_commute h j k]
      simp only [mul_assoc]
    _ = _ := by
      rw [hY']
      simp only [← mul_assoc, firstBlock_rectangle_product]

end Matrices

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
