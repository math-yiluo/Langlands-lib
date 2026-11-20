import Langlands.Global.ArchimedeanVectorSmooth
import Langlands.Global.ArchimedeanSmoothDifferential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.VectorField

/-! # Right differentiation of normed vector-valued archimedean functions -/

noncomputable section

universe uF uV uW

open scoped Classical Manifold ContDiff Matrix.Norms.Operator
open Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℂ W]

local notation "G" => Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F)
local notation "A" => ArchimedeanMatrix F n

/-- The vector-valued expression of a smooth function in the open units chart. -/
def vectorCoordinateExtension (f : VectorSmoothFunctions F n V) : A → V :=
  fun a => f.val ((archimedeanGLCoordinates F n).symm ((unitsChart F n).symm a))

@[simp]
theorem vectorCoordinateExtension_apply (f : VectorSmoothFunctions F n V)
    (g : ArchimedeanGL F n) :
    vectorCoordinateExtension F n f (g : A) = f.val ((archimedeanGLCoordinates F n).symm g) := by
  simp only [vectorCoordinateExtension, unitsChart,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

theorem vectorCoordinateExtension_contDiffAt (f : VectorSmoothFunctions F n V)
    (g : ArchimedeanGL F n) : ContDiffAt ℝ ∞ (vectorCoordinateExtension F n f) (g : A) :=
  (f.property.comp_contMDiffOn
    (contMDiffOn_isOpenEmbedding_symm (I := 𝓘(ℝ, A))
      Units.isOpenEmbedding_val)).contDiffOn.contDiffAt
    (Units.isOpenEmbedding_val.isOpen_range.mem_nhds ⟨g, rfl⟩)

/-- The pointwise derivative in the tangent direction `g * X`. -/
def vectorDirectionalValue (X : RealLieAlgebra F n) (f : VectorSmoothFunctions F n V)
    (g : G) : V :=
  fderiv ℝ (vectorCoordinateExtension F n f) (archimedeanGLCoordinates F n g : A)
    ((archimedeanGLCoordinates F n g : A) * realLieAlgebraToMatrix F n X)

private theorem vectorDirectionalValue_mem (X : RealLieAlgebra F n)
    (f : VectorSmoothFunctions F n V) :
    vectorDirectionalValue F n X f ∈ vectorSmoothFunctions F n V := by
  change ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, V) ∞ _
  intro g
  have h := ((vectorCoordinateExtension_contDiffAt F n f g).fderiv_right
    (m := ∞) (by simp)).clm_apply
      (contDiffAt_id.mul (contDiffAt_const (c := realLieAlgebraToMatrix F n X)))
  have hcomp := h.comp_contMDiffAt (Units.contMDiff_val (𝕜 := ℝ) (n := ∞) g)
  simpa only [Function.comp_def, vectorDirectionalValue,
    ContinuousMulEquiv.apply_symm_apply] using! hcomp

/-- Right differentiation on the original smooth vector functions. -/
def vectorSmoothDifferential (X : RealLieAlgebra F n) :
    Module.End ℂ (VectorSmoothFunctions F n V) where
  toFun f := ⟨vectorDirectionalValue F n X f, vectorDirectionalValue_mem F n X f⟩
  map_add' f h := by
    apply Subtype.ext
    funext g
    change fderiv ℝ (vectorCoordinateExtension F n f + vectorCoordinateExtension F n h)
      (archimedeanGLCoordinates F n g : A) _ = _
    rw [fderiv_add
      ((vectorCoordinateExtension_contDiffAt F n f _).differentiableAt (by simp))
      ((vectorCoordinateExtension_contDiffAt F n h _).differentiableAt (by simp))]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext g
    change fderiv ℝ (c • vectorCoordinateExtension F n f) (archimedeanGLCoordinates F n g : A)
      _ = _
    rw [fderiv_const_smul
      ((vectorCoordinateExtension_contDiffAt F n f _).differentiableAt (by simp))]
    rfl

@[simp]
theorem vectorSmoothDifferential_apply (X : RealLieAlgebra F n) (f : VectorSmoothFunctions F n V)
    (g : G) : (vectorSmoothDifferential F n X f).val g = vectorDirectionalValue F n X f g := rfl

/-- Any extension agreeing on invertible matrices gives the same derivative. -/
theorem vectorSmoothDifferential_eq_of_extension (X : RealLieAlgebra F n)
    (f : VectorSmoothFunctions F n V) (q : A → V)
    (hq : ∀ h : ArchimedeanGL F n, q (h : A) = f.val ((archimedeanGLCoordinates F n).symm h))
    (g : G) :
    (vectorSmoothDifferential F n X f).val g =
      fderiv ℝ q (archimedeanGLCoordinates F n g : A)
        ((archimedeanGLCoordinates F n g : A) * realLieAlgebraToMatrix F n X) := by
  have heq : vectorCoordinateExtension F n f =ᶠ[𝓝 (archimedeanGLCoordinates F n g : A)] q := by
    filter_upwards [Units.isOpenEmbedding_val.isOpen_range.mem_nhds
      (show (archimedeanGLCoordinates F n g : A) ∈
        Set.range (Units.val : ArchimedeanGL F n → A) from ⟨_, rfl⟩)] with a ha
    obtain ⟨h, rfl⟩ := ha
    rw [vectorCoordinateExtension_apply, hq]
  rw [vectorSmoothDifferential_apply, vectorDirectionalValue, heq.fderiv_eq]

/-- Continuous coefficient maps commute with right differentiation. -/
theorem vectorSmoothDifferential_map (X : RealLieAlgebra F n) (T : V →L[ℂ] W)
    (f : VectorSmoothFunctions F n V) :
    vectorSmoothDifferential F n X (vectorSmoothMap F n V T f) =
      vectorSmoothMap F n V T (vectorSmoothDifferential F n X f) := by
  apply Subtype.ext
  funext g
  rw [vectorSmoothDifferential_eq_of_extension F n X _
    (fun a => T (vectorCoordinateExtension F n f a))
    (fun h => by rw [vectorCoordinateExtension_apply]; rfl)]
  have h := (T.restrictScalars ℝ).hasFDerivAt.comp
    (archimedeanGLCoordinates F n g : A)
    ((vectorCoordinateExtension_contDiffAt F n f
      (archimedeanGLCoordinates F n g)).differentiableAt (by simp)).hasFDerivAt
  exact congrArg (fun D : A →L[ℝ] W =>
    D ((archimedeanGLCoordinates F n g : A) * realLieAlgebraToMatrix F n X)) h.fderiv

/-- Left multiplication pulls a smooth vector function back to a smooth vector function. -/
def vectorSmoothLeftTranslation (a : G) : Module.End ℂ (VectorSmoothFunctions F n V) where
  toFun f := ⟨fun x => f.val (a * x), by
    change ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, V) ∞
      (fun x : ArchimedeanGL F n => f.val (a * (archimedeanGLCoordinates F n).symm x))
    have ha : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, A) ∞
        (fun x : ArchimedeanGL F n => archimedeanGLCoordinates F n a * x) :=
      contMDiff_const.mul contMDiff_id
    simpa only [Function.comp_def, map_mul, ContinuousMulEquiv.symm_apply_apply]
      using f.property.comp ha⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem vectorSmoothLeftTranslation_apply (a g : G) (f : VectorSmoothFunctions F n V) :
    (vectorSmoothLeftTranslation F n a f).val g = f.val (a * g) := rfl

/-- Right differentiation commutes with left pullback. -/
theorem vectorSmoothDifferential_leftTranslation (X : RealLieAlgebra F n) (a : G)
    (f : VectorSmoothFunctions F n V) :
    vectorSmoothDifferential F n X (vectorSmoothLeftTranslation F n a f) =
      vectorSmoothLeftTranslation F n a (vectorSmoothDifferential F n X f) := by
  apply Subtype.ext
  funext g
  have hext (h : ArchimedeanGL F n) :
      vectorCoordinateExtension F n f ((archimedeanGLCoordinates F n a : A) * (h : A)) =
        (vectorSmoothLeftTranslation F n a f).val ((archimedeanGLCoordinates F n).symm h) := by
    change vectorCoordinateExtension F n f
      ((archimedeanGLCoordinates F n a * h : ArchimedeanGL F n) : A) = _
    simp only [vectorCoordinateExtension_apply, vectorSmoothLeftTranslation_apply, map_mul,
      ContinuousMulEquiv.symm_apply_apply]
  rw [vectorSmoothDifferential_eq_of_extension F n X (vectorSmoothLeftTranslation F n a f)
    (fun h => vectorCoordinateExtension F n f ((archimedeanGLCoordinates F n a : A) * h)) hext]
  simp only [vectorSmoothLeftTranslation_apply, vectorSmoothDifferential_apply,
    vectorDirectionalValue, map_mul, Units.val_mul]
  let L : A →L[ℝ] A := (ContinuousLinearMap.mul ℝ A) (archimedeanGLCoordinates F n a : A)
  have hf := ((vectorCoordinateExtension_contDiffAt F n f
    (archimedeanGLCoordinates F n a * archimedeanGLCoordinates F n g)).differentiableAt
    (by simp)).hasFDerivAt
  have h := hf.comp (archimedeanGLCoordinates F n g : A) L.hasFDerivAt
  have hL (v : A) : L v = (archimedeanGLCoordinates F n a : A) * v := rfl
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, hL, Units.val_mul,
    mul_assoc] using congrArg
      (fun D : A →L[ℝ] V =>
        D ((archimedeanGLCoordinates F n g : A) * realLieAlgebraToMatrix F n X)) h.fderiv

/-- Pointwise differentiation along any curve with the specified real matrix tangent. -/
theorem vectorSmoothDifferential_hasDerivAt (X : RealLieAlgebra F n) (c : ℝ → G)
    (hc0 : c 0 = 1) (hc : HasDerivAt (fun t => (archimedeanGLCoordinates F n (c t) : A))
      (realLieAlgebraToMatrix F n X) 0) (f : VectorSmoothFunctions F n V) (g : G) :
    HasDerivAt (fun t => f.val (g * c t)) ((vectorSmoothDifferential F n X f).val g) 0 := by
  have hp := hc.const_mul (archimedeanGLCoordinates F n g : A)
  have hzero : (archimedeanGLCoordinates F n (c 0) : A) = 1 := by simp [hc0]
  have hf := ((vectorCoordinateExtension_contDiffAt F n f
    (archimedeanGLCoordinates F n g)).differentiableAt (by simp)).hasFDerivAt
  have hd := hf.comp_hasDerivAt_of_eq (0 : ℝ) hp (by simp only [hzero, mul_one])
  have he : (fun t : ℝ => vectorCoordinateExtension F n f
      ((archimedeanGLCoordinates F n g : A) * (archimedeanGLCoordinates F n (c t) : A))) =
      (fun t : ℝ => f.val (g * c t)) := by
    funext t
    rw [← Units.val_mul, ← map_mul, vectorCoordinateExtension_apply,
      ContinuousMulEquiv.symm_apply_apply]
  rw [Function.comp_def, he] at hd
  exact hd

private theorem vectorSmoothDifferential_commutator (X Y : RealLieAlgebra F n)
    (f : VectorSmoothFunctions F n V) (g : G) :
    (vectorSmoothDifferential F n ⁅X, Y⁆ f).val g =
      (vectorSmoothDifferential F n X (vectorSmoothDifferential F n Y f)).val g -
        (vectorSmoothDifferential F n Y (vectorSmoothDifferential F n X f)).val g := by
  have hext (Z : RealLieAlgebra F n) (h : ArchimedeanGL F n) :
      fderiv ℝ (vectorCoordinateExtension F n f) (h : A)
          ((h : A) * realLieAlgebraToMatrix F n Z) =
        (vectorSmoothDifferential F n Z f).val ((archimedeanGLCoordinates F n).symm h) := by
    simp only [vectorSmoothDifferential_apply, vectorDirectionalValue,
      ContinuousMulEquiv.apply_symm_apply]
  rw [vectorSmoothDifferential_eq_of_extension F n X (vectorSmoothDifferential F n Y f)
      (fun h => fderiv ℝ (vectorCoordinateExtension F n f) h (h * realLieAlgebraToMatrix F n Y))
      (hext Y),
    vectorSmoothDifferential_eq_of_extension F n Y (vectorSmoothDifferential F n X f)
      (fun h => fderiv ℝ (vectorCoordinateExtension F n f) h (h * realLieAlgebraToMatrix F n X))
      (hext X), vectorSmoothDifferential_apply, vectorDirectionalValue, realLieAlgebraToMatrix_lie]
  let X' := realLieAlgebraToMatrix F n X
  let Y' := realLieAlgebraToMatrix F n Y
  let g' : A := archimedeanGLCoordinates F n g
  have hbr :
      VectorField.lieBracket ℝ (fun h : A => h * X') (fun h => h * Y') g' =
        g' * (X' * Y' - Y' * X') := by
    change fderiv ℝ ((ContinuousLinearMap.mul ℝ A).flip Y') g' (g' * X') -
      fderiv ℝ ((ContinuousLinearMap.mul ℝ A).flip X') g' (g' * Y') = _
    simp [ContinuousLinearMap.fderiv, mul_sub, mul_assoc]
  have h := VectorField.fderiv_apply_lieBracket
    (vectorCoordinateExtension_contDiffAt F n f (archimedeanGLCoordinates F n g)) (by simp)
    (differentiableAt_id.mul_const Y') (differentiableAt_id.mul_const X')
  change fderiv ℝ (vectorCoordinateExtension F n f) g'
    (VectorField.lieBracket ℝ (fun h : A => h * X') (fun h => h * Y') g') = _ at h
  rw [hbr] at h
  exact h

/-- The real matrix Lie algebra acts by the actual right differential. -/
def realVectorSmoothLieAction : RealLieAlgebra F n →ₗ⁅ℝ⁆ Module.End ℂ (VectorSmoothFunctions F n V) where
  toFun := vectorSmoothDifferential F n
  map_add' X Y := by
    ext f g
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
      vectorSmoothDifferential_apply, vectorDirectionalValue, map_add, mul_add]
  map_smul' c X := by
    ext f g
    change _ = c • (vectorSmoothDifferential F n X f).val g
    simp only [vectorSmoothDifferential_apply, vectorDirectionalValue, map_smul, mul_smul_comm]
  map_lie' := by
    intro X Y
    ext f g
    exact vectorSmoothDifferential_commutator F n X Y f g

@[simp]
theorem realVectorSmoothLieAction_apply (X : RealLieAlgebra F n) :
    (realVectorSmoothLieAction F n : RealLieAlgebra F n →ₗ⁅ℝ⁆
      Module.End ℂ (VectorSmoothFunctions F n V)) X = vectorSmoothDifferential F n X := rfl

end Langlands.Global.ArchimedeanGL
