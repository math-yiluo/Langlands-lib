import Langlands.Group.GL.MirabolicRadical
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Determinants of the actual block-sum and mirabolic embeddings -/

namespace Langlands.Derivative.JacquetNormalization

open GeneralLinear GeneralLinear.Mirabolic

universe uF

variable {R : Type uF} [CommRing R]

/-- The actual block sum has the product of the two actual determinants. -/
theorem determinant_blockSum {n m : ℕ} (g : GeneralLinear n R)
    (h : GeneralLinear m R) :
    GeneralLinear.determinant (GeneralLinear.blockSum (g, h)) =
      GeneralLinear.determinant g * GeneralLinear.determinant h := by
  apply Units.ext
  change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks g.val 0 0 h.val)) = Matrix.det g.val * Matrix.det h.val
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

/-- Appending the final scalar one in the actual Levi embedding preserves determinant. -/
theorem determinant_levi {n : ℕ} (g : GeneralLinear n R) :
    GeneralLinear.determinant (levi g).val = GeneralLinear.determinant g := by
  change GeneralLinear.determinant (GeneralLinear.blockSum (g, (1 : GeneralLinear 1 R))) = _
  rw [determinant_blockSum, map_one, mul_one]

/-- The successor embedding used by `Φ⁻` preserves determinant. -/
theorem determinant_successor {n : ℕ} (h : mirabolic n R) :
    GeneralLinear.determinant (successor h).val = GeneralLinear.determinant h.val :=
  determinant_levi h.val

end Langlands.Derivative.JacquetNormalization
