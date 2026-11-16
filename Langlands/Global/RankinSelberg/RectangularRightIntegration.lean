import Langlands.Global.RankinSelberg.UnfoldingDual
import Langlands.Global.RankinSelberg.DualExpansionFinal
import Langlands.Global.RankinSelberg.RectangleModulusProof
import Langlands.Group.GL.LowerTriangularBlockCoordinates

/-! # Right translation in nonnegative rectangular integrals -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance rightRectangleSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance rightRectangleSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

local instance rightRectangleMeasurableSpace (F : Type u) [Field F]
    [NumberField F] (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

local instance rightRectangleBorelSpace (F : Type u) [Field F]
    [NumberField F] (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

variable (F : Type u) [Field F] [NumberField F]

/-- Right multiplication of the leading block multiplies the rectangular
coordinate by the same matrix. -/
theorem rectangularPoint_mul_pad_right {r t : ℕ} (h : t < r)
    (g a : Points F (t + 1))
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) :
    rectangularPoint F h g x * pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) a =
      rectangularPoint F h (g * a)
        (x * (GeneralLinearGroupPoints.adelicEquiv F (t + 1) a).val) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [map_mul, adelicEquiv_pad]
  simp only [rectangularPoint, MulEquiv.apply_symm_apply, map_mul]
  rw [← reindex_rankInclusion_rankInclusion (d := r - (t + 1)) (by omega)
      (Nat.le_of_lt (Nat.succ_lt_succ h)), ← map_mul,
    GeneralLinear.lowerBlockLocalization, GeneralLinear.lowerBlockLocalization, ← map_mul,
    rankInclusion_eq_lowerBlockPair (d := r - (t + 1))
      (GeneralLinearGroupPoints.adelicEquiv F (t + 1) a),
    GeneralLinear.lowerBlockPair_mul_lowerBlockPair]
  simp

/-- Integrate along the fixed rectangular unipotent followed by padding. -/
def rectangularRightIntegral {r t : ℕ} (h : t < r)
    (Ξ : Points F (r + 1) → ℝ≥0∞) (g : Points F (t + 1)) : ℝ≥0∞ :=
  ∫⁻ x, Ξ (rectangularPoint F h 1 x *
    pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g)
    ∂rectangleMeasure F (r - (t + 1)) (t + 1)

variable [CompactSpace (AdeleQuotient F)]

/-- The lower-integral change of variables for right multiplication of the
rectangular coordinates, including its determinant factor. -/
theorem lintegral_rectangle_mul_right {k m : ℕ}
    (f : Matrix (Fin k) (Fin m) (Adeles F) → ℝ≥0∞) (hf : Measurable f)
    (g : Points F m) :
    (∫⁻ x, f (x * (GeneralLinearGroupPoints.adelicEquiv F m g).val)
      ∂rectangleMeasure F k m) =
      ENNReal.ofReal ((detNorm F m g ^ k)⁻¹) *
        ∫⁻ x, f x ∂rectangleMeasure F k m := by
  have hg : Measurable (fun x : Matrix (Fin k) (Fin m) (Adeles F) =>
      x * (GeneralLinearGroupPoints.adelicEquiv F m g).val) :=
    (continuous_id.matrix_mul continuous_const).measurable
  rw [← lintegral_map hf hg,
    rectangleMeasureModulus F k m g, lintegral_smul_measure]
  rfl

/-- Right translation of the fixed rectangular unipotent equals the original
rectangular integral times the exact inverse determinant factor. -/
theorem rectangularRightIntegral_eq {r t : ℕ} (h : t < r)
    (Ξ : Points F (r + 1) → ℝ≥0∞) (hΞ : Measurable Ξ)
    (g : Points F (t + 1)) :
    rectangularRightIntegral F h Ξ g =
      ENNReal.ofReal ((detNorm F (t + 1) g ^ (r - (t + 1)))⁻¹) *
        ∫⁻ x, Ξ (rectangularPoint F h g x)
          ∂rectangleMeasure F (r - (t + 1)) (t + 1) := by
  unfold rectangularRightIntegral
  simp_rw [rectangularPoint_mul_pad_right, one_mul]
  refine lintegral_rectangle_mul_right F (fun x => Ξ (rectangularPoint F h g x)) ?_ g
  exact hΞ.comp ((continuous_rectangularPoint F h).comp
    (continuous_const.prodMk continuous_id)).measurable

/-- Moving a right translation of the leading block through the rectangular
integral produces the inverse determinant factor. -/
theorem lintegral_rectangularPoint_mul_right {r t : ℕ} (h : t < r)
    (Ξ : Points F (r + 1) → ℝ≥0∞) (hΞ : Measurable Ξ)
    (g a : Points F (t + 1)) :
    (∫⁻ x, Ξ (rectangularPoint F h g x *
      pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) a)
      ∂rectangleMeasure F (r - (t + 1)) (t + 1)) =
      ENNReal.ofReal ((detNorm F (t + 1) a ^ (r - (t + 1)))⁻¹) *
        ∫⁻ x, Ξ (rectangularPoint F h (g * a) x)
          ∂rectangleMeasure F (r - (t + 1)) (t + 1) := by
  simp_rw [rectangularPoint_mul_pad_right]
  refine lintegral_rectangle_mul_right F (fun x => Ξ (rectangularPoint F h (g * a) x)) ?_ a
  exact hΞ.comp ((continuous_rectangularPoint F h).comp
    (continuous_const.prodMk continuous_id)).measurable

/-- A determinant-one padded right symmetry is preserved by rectangular
integration. -/
theorem lintegral_rectangularPoint_right_invariant {r t : ℕ} (h : t < r)
    (Ξ : Points F (r + 1) → ℝ≥0∞) (hΞ : Measurable Ξ)
    (a : Points F (t + 1)) (ha : detNorm F (t + 1) a = 1)
    (hinv : ∀ y : Points F (r + 1),
      Ξ (y * pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) a) = Ξ y)
    (g : Points F (t + 1)) :
    (∫⁻ x, Ξ (rectangularPoint F h (g * a) x)
      ∂rectangleMeasure F (r - (t + 1)) (t + 1)) =
      ∫⁻ x, Ξ (rectangularPoint F h g x)
        ∂rectangleMeasure F (r - (t + 1)) (t + 1) := by
  have he := lintegral_rectangularPoint_mul_right F h Ξ hΞ g a
  simp only [hinv, ha, one_pow, inv_one, ENNReal.ofReal_one, one_mul] at he
  exact he.symm

end Langlands.Global.RankinSelbergGlobal
