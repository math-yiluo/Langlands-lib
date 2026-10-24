import Langlands.ClassField.Global.FullLogGaloisAction

/-! # Splitting full logarithmic coordinates into mean and sum-zero parts -/

noncomputable section

open NumberField
open scoped Classical

namespace Langlands.ClassField.Global

universe u v

variable (E : Type v) [Field E]

/-- Embed a real scalar as a constant infinite-place vector. -/
def fullLogConstant : ℝ →ₗ[ℝ] (InfinitePlace E → ℝ) where
  toFun a _ := a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem fullLogConstant_apply (a : ℝ) (w : InfinitePlace E) :
    fullLogConstant E a w = a := rfl

variable [NumberField E]

/-- The mean of all infinite-place coordinates. -/
def fullLogMean : (InfinitePlace E → ℝ) →ₗ[ℝ] ℝ :=
  (Fintype.card (InfinitePlace E) : ℝ)⁻¹ • infiniteLogSum E

@[simp] theorem fullLogMean_constant (a : ℝ) :
    fullLogMean E (fullLogConstant E a) = a := by
  simp [fullLogMean, infiniteLogSum, fullLogConstant, nsmul_eq_mul]

theorem mem_fullLogHyperplane_iff_mean_eq_zero (x : InfinitePlace E → ℝ) :
    x ∈ fullLogHyperplane E ↔ fullLogMean E x = 0 := by
  change infiniteLogSum E x = 0 ↔
    (Fintype.card (InfinitePlace E) : ℝ)⁻¹ * infiniteLogSum E x = 0
  simp

@[simp] theorem fullLogMean_hyperplane (x : fullLogHyperplane E) :
    fullLogMean E x = 0 :=
  (mem_fullLogHyperplane_iff_mean_eq_zero E x).mp x.2

/-- Subtract the constant mean to obtain the sum-zero part. -/
def fullLogCentered : (InfinitePlace E → ℝ) →ₗ[ℝ] fullLogHyperplane E :=
  (LinearMap.id - (fullLogConstant E).comp (fullLogMean E)).codRestrict
    (fullLogHyperplane E) (by
      intro x
      rw [mem_fullLogHyperplane_iff_mean_eq_zero]
      change fullLogMean E (x - fullLogConstant E (fullLogMean E x)) = 0
      simp)

@[simp] theorem fullLogCentered_apply (x : InfinitePlace E → ℝ) :
    (fullLogCentered E x : InfinitePlace E → ℝ) =
      x - fullLogConstant E (fullLogMean E x) := rfl

@[simp] theorem fullLogCentered_hyperplane (x : fullLogHyperplane E) :
    fullLogCentered E x = x := by
  apply Subtype.ext
  simp

@[simp] theorem fullLogCentered_constant (a : ℝ) :
    fullLogCentered E (fullLogConstant E a) = 0 := by
  apply Subtype.ext
  simp

/-- Full coordinates split as the sum-zero part and a scalar constant part. -/
def fullLogSplit : (InfinitePlace E → ℝ) ≃ₗ[ℝ] (fullLogHyperplane E × ℝ) where
  toFun x := (fullLogCentered E x, fullLogMean E x)
  invFun x := x.1 + fullLogConstant E x.2
  left_inv x := by simp
  right_inv x := by ext <;> simp
  map_add' x y := by simp
  map_smul' a x := by simp

@[simp] theorem fullLogSplit_apply (x : InfinitePlace E → ℝ) :
    fullLogSplit E x = (fullLogCentered E x, fullLogMean E x) := rfl

@[simp] theorem fullLogSplit_symm_apply (x : fullLogHyperplane E × ℝ) :
    (fullLogSplit E).symm x = x.1 + fullLogConstant E x.2 := rfl

variable (F : Type u) [Field F] [Algebra F E]

omit [NumberField E] in
@[simp] theorem fullLogPermutation_constant (g : E ≃ₐ[F] E) (a : ℝ) :
    fullLogPermutation F E g (fullLogConstant E a) = fullLogConstant E a := rfl

@[simp] theorem fullLogMean_permutation (g : E ≃ₐ[F] E) (x : InfinitePlace E → ℝ) :
    fullLogMean E (fullLogPermutation F E g x) = fullLogMean E x := by
  change _ * infiniteLogSum E (fullLogPermutation F E g x) =
    _ * infiniteLogSum E x
  rw [infiniteLogSum_permutation]

theorem fullLogCentered_equivariant (g : E ≃ₐ[F] E) (x : InfinitePlace E → ℝ) :
    fullLogCentered E (fullLogPermutation F E g x) =
      fullLogHyperplaneAut F E g (fullLogCentered E x) := by
  apply Subtype.ext
  simp

/-- The arithmetic action is diagonal in this splitting and fixes the scalar part. -/
theorem fullLogSplit_equivariant (g : E ≃ₐ[F] E) (x : InfinitePlace E → ℝ) :
    fullLogSplit E (fullLogPermutation F E g x) =
      (fullLogHyperplaneAut F E g (fullLogSplit E x).1, (fullLogSplit E x).2) := by
  simp [fullLogCentered_equivariant]

end Langlands.ClassField.Global
