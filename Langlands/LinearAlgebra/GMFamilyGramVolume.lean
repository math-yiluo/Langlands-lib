import Langlands.LinearAlgebra.GMFamilies
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic

/-! # Gram volumes of finite vector families -/

noncomputable section

open scoped RealInnerProductSpace
open Classical

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Reindexing a family preserves its Gram volume. -/
theorem gramVolume_reindex (e : ι ≃ κ) (v : κ → E) :
    gramVolume (v ∘ e) = gramVolume v := by
  unfold gramVolume
  exact congrArg Real.sqrt (Matrix.det_submatrix_equiv_self e (Matrix.gram ℝ v))

/-- The Gram volume is positive precisely for an independent family. -/
theorem gramVolume_pos_iff (v : ι → E) : 0 < gramVolume v ↔ LinearIndependent ℝ v := by
  change 0 < Real.sqrt (Matrix.gram ℝ v).det ↔ _
  rw [Real.sqrt_pos, lt_iff_le_and_ne, and_iff_right (Matrix.posSemidef_gram ℝ v).det_nonneg,
    ne_comm, Matrix.det_gram_ne_zero_iff_linearIndependent]

/-- A Gram volume with a subspace as ambient space is the same as in the full space. -/
theorem gramVolume_subtype (W : Submodule ℝ E) (v : ι → W) :
    gramVolume (fun i => (v i : E)) = gramVolume v := rfl

/-- The determinant in orthonormal coordinates gives the Gram volume. -/
theorem gramVolume_eq_abs_det (b : OrthonormalBasis ι ℝ E) (v : ι → E) :
    gramVolume v = |b.toBasis.det v| := by
  change Real.sqrt (Matrix.gram ℝ v).det = _
  rw [Matrix.gram_eq_conjTranspose_mul b v, Matrix.det_mul, Matrix.det_conjTranspose,
    Module.Basis.det_apply]
  change Real.sqrt ((b.toBasis.toMatrix v).det * (b.toBasis.toMatrix v).det) = _
  rw [← sq, Real.sqrt_sq_eq_abs]

/-- Replacing one basis vector multiplies the Gram volume by the absolute value of the
    replacement's coordinate in the original basis. -/
theorem gramVolume_update_basis (b : Module.Basis ι ℝ E) (i : ι) (x : E) :
    gramVolume (Function.update (fun j => b j) i x) = |b.coord i x| * gramVolume (fun j => b j) := by
  let : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  let q : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex
    (Fintype.equivOfCardEq (by simp [Module.finrank_eq_card_basis b]))
  have hb : Module.Basis.mk b.linearIndependent b.span_eq.ge = b := by
    ext
    simp
  have h := q.toBasis.det_smul_mk_coord_eq_det_update b.linearIndependent b.span_eq.ge i
  rw [hb] at h
  have he := congrArg (fun l : E →ₗ[ℝ] ℝ => l x) h
  change q.toBasis.det (fun j => b j) * b.coord i x =
    q.toBasis.det (Function.update (fun j => b j) i x) at he
  rw [gramVolume_eq_abs_det q, gramVolume_eq_abs_det q, ← he, abs_mul, mul_comm]

end Langlands.GMFamily
