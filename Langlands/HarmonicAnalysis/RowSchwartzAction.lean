import Langlands.Group.GL.Basic
import Langlands.Representation.Hecke.TestFunction
import Mathlib.RepresentationTheory.Subrepresentation

/-! The actual row action on Schwartz–Bruhat functions and evaluation at zero. -/

noncomputable section

namespace Langlands.HarmonicAnalysis

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ}

/-- Right multiplication by an invertible matrix is a homeomorphism of row space. -/
def rowHomeomorph (g : Langlands.GeneralLinear n F) :
    (Fin n → F) ≃ₜ (Fin n → F) where
  toFun x := Matrix.vecMul x g.val
  invFun x := Matrix.vecMul x (g⁻¹).val
  left_inv x := by
    dsimp only
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.vecMul_one]
  right_inv x := by
    dsimp only
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.vecMul_one]
  continuous_toFun := continuous_id.matrix_vecMul continuous_const
  continuous_invFun := continuous_id.matrix_vecMul continuous_const

@[simp] theorem rowHomeomorph_apply (g : Langlands.GeneralLinear n F) (x : Fin n → F) :
    rowHomeomorph g x = Matrix.vecMul x g.val := rfl

/-- The row translate has convention `(R_g Φ)(x) = Φ(xg)`. -/
def rowTranslate (g : Langlands.GeneralLinear n F) :
    SchwartzBruhat (Fin n → F) ≃ₗ[ℂ] SchwartzBruhat (Fin n → F) :=
  Hecke.TestFunction.pullback (rowHomeomorph g)

@[simp] theorem rowTranslate_apply (g : Langlands.GeneralLinear n F)
    (Φ : SchwartzBruhat (Fin n → F)) (x : Fin n → F) :
    rowTranslate g Φ x = Φ (Matrix.vecMul x g.val) := rfl

@[simp] theorem rowTranslate_one (Φ : SchwartzBruhat (Fin n → F)) :
    rowTranslate 1 Φ = Φ := by
  ext x
  simp

theorem rowTranslate_mul (g h : Langlands.GeneralLinear n F)
    (Φ : SchwartzBruhat (Fin n → F)) :
    rowTranslate (g * h) Φ = rowTranslate g (rowTranslate h Φ) := by
  ext x
  simp only [rowTranslate_apply, Units.val_mul, Matrix.vecMul_vecMul]

/-- Bundled linear representation associated with the actual row translations. -/
def rowSchwartzRepresentation :
    Representation ℂ (Langlands.GeneralLinear n F) (SchwartzBruhat (Fin n → F)) where
  toFun g := (rowTranslate g).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro Φ
    exact rowTranslate_one Φ
  map_mul' g h := by
    apply LinearMap.ext
    intro Φ
    exact rowTranslate_mul g h Φ

@[simp] theorem rowSchwartzRepresentation_apply (g : Langlands.GeneralLinear n F)
    (Φ : SchwartzBruhat (Fin n → F)) :
    rowSchwartzRepresentation g Φ = rowTranslate g Φ := rfl

/-- Evaluation of a row test function at the zero row. -/
def rowEvaluationAtZero : SchwartzBruhat (Fin n → F) →ₗ[ℂ] ℂ where
  toFun Φ := Φ 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalRing F] in
@[simp] theorem rowEvaluationAtZero_apply (Φ : SchwartzBruhat (Fin n → F)) :
    rowEvaluationAtZero Φ = Φ 0 := rfl

@[simp] theorem rowEvaluationAtZero_translate (g : Langlands.GeneralLinear n F)
    (Φ : SchwartzBruhat (Fin n → F)) :
    rowEvaluationAtZero (rowTranslate g Φ) = rowEvaluationAtZero Φ := by
  simp [rowEvaluationAtZero]

/-- The test functions vanishing at zero form a stable linear subspace. -/
def rowVanishingAtZero : Subrepresentation (rowSchwartzRepresentation (F := F) (n := n)) where
  toSubmodule := LinearMap.ker rowEvaluationAtZero
  apply_mem_toSubmodule g := by
    intro Φ hΦ
    change rowEvaluationAtZero (rowTranslate g Φ) = 0
    rw [rowEvaluationAtZero_translate]
    exact hΦ

@[simp] theorem mem_rowVanishingAtZero (Φ : SchwartzBruhat (Fin n → F)) :
    Φ ∈ rowVanishingAtZero ↔ Φ 0 = 0 := Iff.rfl

/-- Any test function specified pointwise as a row translate is the bundled translate. -/
theorem eq_rowTranslate_iff (g : Langlands.GeneralLinear n F)
    (Φ Ψ : SchwartzBruhat (Fin n → F)) :
    Ψ = rowTranslate g Φ ↔ ∀ x, Ψ x = Φ (Matrix.vecMul x g.val) := by
  constructor
  · rintro rfl x
    rfl
  · exact fun h => Hecke.TestFunction.ext h

end Langlands.HarmonicAnalysis
