import Langlands.Algebra.LieEnvelopingEquiv
import Langlands.Global.ArchimedeanLieAlgebra
import Mathlib.Algebra.Lie.Prod
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Block inclusions for the actual archimedean Lie algebras -/

noncomputable section
universe u

open scoped Classical Matrix.Norms.Operator TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (F : Type u) [Field F] {a b n : ℕ} (h : a + b = n)

local notation "M" => ArchimedeanMatrix F
local notation "L" => RealLieAlgebra F
local notation "e" => finSumFinEquiv.trans (finCongr h)

/-- Block diagonal insertion in real matrix coordinates. -/
def blockDiagonalMatrixMap : (M a × M b) →ₗ[ℝ] M n where
  toFun p := Matrix.reindex e e (Matrix.fromBlocks p.1 0 0 p.2)
  map_add' p q := by
    change Matrix.reindexLinearEquiv ℝ _ e e (Matrix.fromBlocks (p.1 + q.1) 0 0 (p.2 + q.2)) =
      Matrix.reindexLinearEquiv ℝ _ e e (Matrix.fromBlocks p.1 0 0 p.2) +
        Matrix.reindexLinearEquiv ℝ _ e e (Matrix.fromBlocks q.1 0 0 q.2)
    rw [← map_add, Matrix.fromBlocks_add, zero_add, zero_add]
  map_smul' c p := by
    change Matrix.reindexLinearEquiv ℝ _ e e (Matrix.fromBlocks (c • p.1) 0 0 (c • p.2)) =
      c • Matrix.reindexLinearEquiv ℝ _ e e (Matrix.fromBlocks p.1 0 0 p.2)
    rw [← map_smul, Matrix.fromBlocks_smul, smul_zero, smul_zero]

theorem blockDiagonalMatrixMap_apply (p : M a × M b) :
    blockDiagonalMatrixMap F h p = Matrix.reindex e e (Matrix.fromBlocks p.1 0 0 p.2) := rfl

theorem blockDiagonalMatrixMap_mul (p q : M a × M b) :
    blockDiagonalMatrixMap F h (p * q) =
      blockDiagonalMatrixMap F h p * blockDiagonalMatrixMap F h q := by
  change Matrix.reindexAlgEquiv ℝ _ e (Matrix.fromBlocks (p.1 * q.1) 0 0 (p.2 * q.2)) =
    Matrix.reindexAlgEquiv ℝ _ e (Matrix.fromBlocks p.1 0 0 p.2) *
      Matrix.reindexAlgEquiv ℝ _ e (Matrix.fromBlocks q.1 0 0 q.2)
  rw [← map_mul, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/-- The Lie algebra map of the two-block diagonal inclusion. -/
def blockDiagonalRealLieMap : (L a × L b) →ₗ⁅ℝ⁆ L n :=
  { (realLieAlgebraToMatrix F n).symm.toLinearMap ∘ₗ blockDiagonalMatrixMap F h ∘ₗ
      ((realLieAlgebraToMatrix F a).prodCongr (realLieAlgebraToMatrix F b)).toLinearMap with
    map_lie' := by
      intro p q
      apply (realLieAlgebraToMatrix F n).injective
      simp only [realLieAlgebraToMatrix_lie, LieAlgebra.Prod.bracket_apply]
      let P := (realLieAlgebraToMatrix F a p.1, realLieAlgebraToMatrix F b p.2)
      let Q := (realLieAlgebraToMatrix F a q.1, realLieAlgebraToMatrix F b q.2)
      change blockDiagonalMatrixMap F h (P * Q - Q * P) =
        blockDiagonalMatrixMap F h P * blockDiagonalMatrixMap F h Q -
          blockDiagonalMatrixMap F h Q * blockDiagonalMatrixMap F h P
      rw [map_sub, blockDiagonalMatrixMap_mul, blockDiagonalMatrixMap_mul] }

/-- Include the first block, with a zero direction in the second block. -/
def firstBlockRealLieInclusion : L a →ₗ⁅ℝ⁆ L n :=
  (blockDiagonalRealLieMap F h).comp (LieHom.inl ℝ (L a) (L b))

/-- Include the second block, with a zero direction in the first block. -/
def secondBlockRealLieInclusion : L b →ₗ⁅ℝ⁆ L n :=
  (blockDiagonalRealLieMap F h).comp (LieHom.inr ℝ (L a) (L b))

theorem firstBlockRealLieInclusion_matrix (X : L a) :
    realLieAlgebraToMatrix F n (firstBlockRealLieInclusion F h X) =
      blockDiagonalMatrixMap F h (realLieAlgebraToMatrix F a X, 0) :=
  LinearEquiv.apply_symm_apply _ _

theorem secondBlockRealLieInclusion_matrix (X : L b) :
    realLieAlgebraToMatrix F n (secondBlockRealLieInclusion F h X) =
      blockDiagonalMatrixMap F h (0, realLieAlgebraToMatrix F b X) :=
  LinearEquiv.apply_symm_apply _ _

private def complexifyBlockLieMap {k : ℕ} (f : L k →ₗ⁅ℝ⁆ L n) :
    ComplexLieAlgebra F k →ₗ⁅ℂ⁆ ComplexLieAlgebra F n :=
  { f.toLinearMap.baseChange ℂ with
    map_lie' := fun {X Y} =>
      (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ) f).map_lie X Y }

/-- Complexification of the first real block inclusion. -/
def firstBlockComplexLieInclusion : ComplexLieAlgebra F a →ₗ⁅ℂ⁆ ComplexLieAlgebra F n :=
  complexifyBlockLieMap F (firstBlockRealLieInclusion F h)

/-- Complexification of the second real block inclusion. -/
def secondBlockComplexLieInclusion : ComplexLieAlgebra F b →ₗ⁅ℂ⁆ ComplexLieAlgebra F n :=
  complexifyBlockLieMap F (secondBlockRealLieInclusion F h)

@[simp]
theorem firstBlockComplexLieInclusion_tmul (c : ℂ) (X : L a) :
    firstBlockComplexLieInclusion F h (c ⊗ₜ[ℝ] X) =
      c ⊗ₜ[ℝ] firstBlockRealLieInclusion F h X := rfl

@[simp]
theorem secondBlockComplexLieInclusion_tmul (c : ℂ) (X : L b) :
    secondBlockComplexLieInclusion F h (c ⊗ₜ[ℝ] X) =
      c ⊗ₜ[ℝ] secondBlockRealLieInclusion F h X := rfl

/-- The universal enveloping map of the first block. -/
def firstBlockEnvelopingInclusion : EnvelopingAlgebra F a →ₐ[ℂ] EnvelopingAlgebra F n :=
  Algebra.LieEnvelopingEquiv.map (firstBlockComplexLieInclusion F h)

/-- The universal enveloping map of the second block. -/
def secondBlockEnvelopingInclusion : EnvelopingAlgebra F b →ₐ[ℂ] EnvelopingAlgebra F n :=
  Algebra.LieEnvelopingEquiv.map (secondBlockComplexLieInclusion F h)

@[simp]
theorem firstBlockEnvelopingInclusion_generator (X : ComplexLieAlgebra F a) :
    firstBlockEnvelopingInclusion F h (envelopingGenerator F a X) =
      envelopingGenerator F n (firstBlockComplexLieInclusion F h X) :=
  Algebra.LieEnvelopingEquiv.map_generator _ _

@[simp]
theorem secondBlockEnvelopingInclusion_generator (X : ComplexLieAlgebra F b) :
    secondBlockEnvelopingInclusion F h (envelopingGenerator F b X) =
      envelopingGenerator F n (secondBlockComplexLieInclusion F h X) :=
  Algebra.LieEnvelopingEquiv.map_generator _ _

/-- The complex span of products of a member of the center ideal on the left
with an arbitrary enveloping element on the right. -/
def centralIdealRightSpan (n : ℕ) (J : Ideal (EnvelopingCenter F n)) :
    Submodule ℂ (EnvelopingAlgebra F n) :=
  Submodule.span ℂ (Set.range fun p : J × EnvelopingAlgebra F n =>
    centerInclusion F n p.1.val * p.2)

end Langlands.Global.ArchimedeanGL
