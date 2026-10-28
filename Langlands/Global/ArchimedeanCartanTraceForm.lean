import Langlands.Global.ArchimedeanCompactLieAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # Trace and positive Cartan forms on the actual matrix Lie algebra -/

noncomputable section
universe u
open NumberField
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K]

local instance : Fintype {v : InfinitePlace K // v.IsReal} := Fintype.ofFinite _
local instance : Fintype {v : InfinitePlace K // v.IsComplex} := Fintype.ofFinite _

/-- The scalar real trace on the mixed real/complex coefficient algebra. -/
def totalMixedTrace : mixedEmbedding.mixedSpace K →ₗ[ℝ] ℝ where
  toFun a := (∑ v, a.1 v) + 2 * ∑ v, (a.2 v).re
  map_add' a b := by simp [Finset.sum_add_distrib, mul_add]; ring
  map_smul' r a := by
    simp [Finset.mul_sum, mul_add, mul_left_comm]

theorem totalMixedTrace_apply (a : mixedEmbedding.mixedSpace K) :
    totalMixedTrace K a = (∑ v, a.1 v) + 2 * ∑ v, (a.2 v).re := rfl

@[simp]
theorem totalMixedTrace_star (a : mixedEmbedding.mixedSpace K) :
    totalMixedTrace K (star a) = totalMixedTrace K a := by
  simp [totalMixedTrace]

theorem totalMixedTrace_mul_star (a : mixedEmbedding.mixedSpace K) :
    totalMixedTrace K (a * star a) =
      (∑ v, a.1 v ^ 2) + 2 * ∑ v, Complex.normSq (a.2 v) := by
  simp [totalMixedTrace_apply, Complex.mul_conj, sq]

theorem totalMixedTrace_mul_star_nonneg (a : mixedEmbedding.mixedSpace K) :
    0 ≤ totalMixedTrace K (a * star a) := by
  rw [totalMixedTrace_mul_star]
  exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _))

theorem totalMixedTrace_mul_star_eq_zero_iff (a : mixedEmbedding.mixedSpace K) :
    totalMixedTrace K (a * star a) = 0 ↔ a = 0 := by
  classical
  constructor
  · intro h
    rw [totalMixedTrace_mul_star] at h
    have hr : 0 ≤ ∑ v, a.1 v ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hc : 0 ≤ ∑ v, Complex.normSq (a.2 v) :=
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have hr0 : ∑ v, a.1 v ^ 2 = 0 := by linarith
    have hc0 : ∑ v, Complex.normSq (a.2 v) = 0 := by linarith
    apply Prod.ext
    · funext v
      have hv := (Finset.sum_eq_zero_iff_of_nonneg
        (fun v _ => sq_nonneg (a.1 v))).mp hr0 v (Finset.mem_univ v)
      exact (sq_eq_zero_iff).mp hv
    · funext v
      exact Complex.normSq_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg
          (fun v _ => Complex.normSq_nonneg (a.2 v))).mp hc0 v (Finset.mem_univ v))
  · rintro rfl
    simp

variable (n : ℕ)

/-- The real invariant matrix trace form, with complex-place weight two. -/
def matrixTraceForm : LinearMap.BilinForm ℝ (RealLieAlgebra K n) :=
  LinearMap.mk₂ ℝ
    (fun X Y => totalMixedTrace K
      (Matrix.trace (realLieAlgebraToMatrix K n X * realLieAlgebraToMatrix K n Y)))
    (by intros; simp [Matrix.add_mul, Matrix.trace_add])
    (by intros; simp [Matrix.trace_smul])
    (by intros; simp [Matrix.mul_add, Matrix.trace_add])
    (by intros; simp [Matrix.trace_smul])

@[simp]
theorem matrixTraceForm_apply (X Y : RealLieAlgebra K n) :
    matrixTraceForm K n X Y = totalMixedTrace K
      (Matrix.trace (realLieAlgebraToMatrix K n X * realLieAlgebraToMatrix K n Y)) := rfl

theorem matrixTraceForm_symm (X Y : RealLieAlgebra K n) :
    matrixTraceForm K n X Y = matrixTraceForm K n Y X := by
  unfold matrixTraceForm
  exact congrArg (totalMixedTrace K) (Matrix.trace_mul_comm _ _)

theorem matrixTraceForm_lie (X Y Z : RealLieAlgebra K n) :
    matrixTraceForm K n ⁅X, Y⁆ Z = matrixTraceForm K n X ⁅Y, Z⁆ := by
  simp only [matrixTraceForm_apply, realLieAlgebraToMatrix_lie, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.trace_sub]
  apply congrArg (totalMixedTrace K)
  rw [Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.trace_mul_comm (realLieAlgebraToMatrix K n Y)
      (realLieAlgebraToMatrix K n X * realLieAlgebraToMatrix K n Z),
    Matrix.mul_assoc]

theorem matrixTraceForm_star (X Y : RealLieAlgebra K n) :
    matrixTraceForm K n (star X) (star Y) = matrixTraceForm K n X Y := by
  change totalMixedTrace K
    (Matrix.trace (star (realLieAlgebraToMatrix K n X) *
      star (realLieAlgebraToMatrix K n Y))) = _
  rw [← star_mul, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose,
    totalMixedTrace_star, Matrix.trace_mul_comm]
  rfl

/-- The positive Cartan twist of the real invariant trace form. -/
def cartanPositiveForm : LinearMap.BilinForm ℝ (RealLieAlgebra K n) :=
  LinearMap.mk₂ ℝ (fun X Y => matrixTraceForm K n X (star Y))
    (by intros; exact LinearMap.BilinForm.add_left _ _ _)
    (by intros; exact LinearMap.BilinForm.smul_left _ _ _)
    (by intros; rw [star_add, LinearMap.BilinForm.add_right])
    (by intros; rw [star_smul, star_trivial, map_smul])

@[simp]
theorem cartanPositiveForm_apply (X Y : RealLieAlgebra K n) :
    cartanPositiveForm K n X Y = matrixTraceForm K n X (star Y) := rfl

theorem cartanPositiveForm_cartanInvolution (X Y : RealLieAlgebra K n) :
    cartanPositiveForm K n X Y = -matrixTraceForm K n X (cartanInvolution K n Y) := by
  rw [cartanPositiveForm_apply, cartanInvolution_apply, map_neg, neg_neg]

theorem cartanPositiveForm_symm (X Y : RealLieAlgebra K n) :
    cartanPositiveForm K n X Y = cartanPositiveForm K n Y X := by
  rw [cartanPositiveForm_apply, cartanPositiveForm_apply,
    ← matrixTraceForm_star K n X (star Y), star_star, matrixTraceForm_symm]

theorem cartanPositiveForm_self_sum (X : RealLieAlgebra K n) :
    cartanPositiveForm K n X X =
      ∑ i, ∑ j, totalMixedTrace K
        (realLieAlgebraToMatrix K n X i j * star (realLieAlgebraToMatrix K n X i j)) := by
  change totalMixedTrace K
    (Matrix.trace (realLieAlgebraToMatrix K n X * star (realLieAlgebraToMatrix K n X))) = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, map_sum]

/-- The Cartan twist retains every real and imaginary matrix coordinate. -/
theorem cartanPositiveForm_self_coordinates (X : RealLieAlgebra K n) :
    cartanPositiveForm K n X X =
      ∑ i, ∑ j, ((∑ v, (realLieAlgebraToMatrix K n X i j).1 v ^ 2) +
        2 * ∑ v, Complex.normSq ((realLieAlgebraToMatrix K n X i j).2 v)) := by
  simp only [cartanPositiveForm_self_sum, totalMixedTrace_mul_star]

theorem cartanPositiveForm_self_nonneg (X : RealLieAlgebra K n) :
    0 ≤ cartanPositiveForm K n X X := by
  rw [cartanPositiveForm_self_sum]
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => totalMixedTrace_mul_star_nonneg K _

theorem cartanPositiveForm_self_eq_zero_iff (X : RealLieAlgebra K n) :
    cartanPositiveForm K n X X = 0 ↔ X = 0 := by
  classical
  constructor
  · intro h
    rw [cartanPositiveForm_self_sum] at h
    apply (realLieAlgebraToMatrix K n).injective
    apply Matrix.ext
    intro i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ =>
        totalMixedTrace_mul_star_nonneg K (realLieAlgebraToMatrix K n X i j))).mp
      h i (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => totalMixedTrace_mul_star_nonneg K (realLieAlgebraToMatrix K n X i j))).mp
      hi j (Finset.mem_univ j)
    exact (totalMixedTrace_mul_star_eq_zero_iff K _).mp hij
  · rintro rfl
    simp

theorem cartanPositiveForm_self_pos {X : RealLieAlgebra K n} (hX : X ≠ 0) :
    0 < cartanPositiveForm K n X X :=
  lt_of_le_of_ne (cartanPositiveForm_self_nonneg K n X)
    (fun h => hX ((cartanPositiveForm_self_eq_zero_iff K n X).mp h.symm))

theorem matrixTraceForm_nondegenerate : (matrixTraceForm K n).Nondegenerate := by
  constructor
  · intro X hX
    exact (cartanPositiveForm_self_eq_zero_iff K n X).mp (hX (star X))
  · intro X hX
    apply (cartanPositiveForm_self_eq_zero_iff K n X).mp
    rw [cartanPositiveForm_apply, matrixTraceForm_symm]
    exact hX (star X)

theorem cartanPositiveForm_nondegenerate : (cartanPositiveForm K n).Nondegenerate := by
  constructor
  · intro X hX
    exact (cartanPositiveForm_self_eq_zero_iff K n X).mp (hX X)
  · intro X hX
    exact (cartanPositiveForm_self_eq_zero_iff K n X).mp (hX X)

theorem matrixTraceForm_compact_right (X Y : RealLieAlgebra K n)
    (hY : Y ∈ compactLieSubalgebra K n) :
    matrixTraceForm K n X Y = -cartanPositiveForm K n X Y := by
  rw [mem_compactLieSubalgebra] at hY
  rw [cartanPositiveForm_apply, hY, map_neg, neg_neg]

theorem matrixTraceForm_complement_right (X Y : RealLieAlgebra K n)
    (hY : Y ∈ cartanComplement K n) :
    matrixTraceForm K n X Y = cartanPositiveForm K n X Y := by
  rw [mem_cartanComplement] at hY
  rw [cartanPositiveForm_apply, hY]

theorem cartanPositiveForm_compact_complement (X Y : RealLieAlgebra K n)
    (hX : X ∈ compactLieSubalgebra K n) (hY : Y ∈ cartanComplement K n) :
    cartanPositiveForm K n X Y = 0 := by
  rw [mem_compactLieSubalgebra] at hX
  rw [mem_cartanComplement] at hY
  have h := matrixTraceForm_star K n X Y
  rw [hX, hY, LinearMap.BilinForm.neg_left] at h
  rw [cartanPositiveForm_apply, hY]
  linarith

theorem cartanPositiveForm_complement_compact (X Y : RealLieAlgebra K n)
    (hX : X ∈ cartanComplement K n) (hY : Y ∈ compactLieSubalgebra K n) :
    cartanPositiveForm K n X Y = 0 := by
  rw [cartanPositiveForm_symm]
  exact cartanPositiveForm_compact_complement K n Y X hY hX

end Langlands.Global.ArchimedeanGL
