import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerDeriv
import Langlands.Global.RankinSelberg.EqualAnalyticFourierDominated
import Langlands.Automorphic.CuspidalL2.Basics

/-! # Character derivatives of Whittaker functions

For a square-zero archimedean column direction, the right derivative of `W_f(diag(γ, I) y ·)`
is a character derivative: it multiplies `W_f(diag(γ, I) y)` by `2πi L`, where `L` is a trace
of the last row of `γ` against the direction. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter Topology Real
open scoped CategoryTheory.MonObj FourierTransform
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints PrimitiveAdelicHeight Langlands.Automorphic.CuspidalWhittaker

local instance charDerivSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance charDerivSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

section Geometry

/-- The archimedean coordinates `y_∞ ∈ GL_n(F_∞)` of an adelic point. -/
def archCoord {n : ℕ} (y : Points F n) : ArchimedeanGL F n :=
  archimedeanGLCoordinates F n
    (AdelicGL.infinite F n (GeneralLinearGroupPoints.adelicEquiv F n y))

variable {r : ℕ} (j : ℕ)

/-- The column of infinite adeles with mixed coordinates `w`. -/
def infCol (w : Fin (r + 1) → mixedEmbedding.mixedSpace F) : Fin (r + 1) → Adeles F :=
  fun a => EqualAnalytic.infiniteAdele F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (w a))

/-- The direction `y_∞⁻¹ colMatrix(w) y_∞`. -/
def colConj (y : Points F (r + 1)) (w : Fin (r + 1) → mixedEmbedding.mixedSpace F) :
    ArchimedeanMatrix F (r + 1) :=
  (((archCoord F y)⁻¹ : ArchimedeanGL F (r + 1)) : ArchimedeanMatrix F (r + 1)) *
    colMatrix j w * ((archCoord F y : ArchimedeanGL F (r + 1)) : ArchimedeanMatrix F (r + 1))

theorem colConj_mul_self (y : Points F (r + 1)) (w : Fin (r + 1) → mixedEmbedding.mixedSpace F) :
    colConj F j y w * colConj F j y w = 0 := by
  simp only [colConj]
  set Y := archCoord F y
  have h : ((Y : ArchimedeanGL F (r + 1)) : ArchimedeanMatrix F (r + 1)) *
      (((Y⁻¹ : ArchimedeanGL F (r + 1))) : ArchimedeanMatrix F (r + 1)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc _ = ((Y⁻¹ : ArchimedeanGL F (r + 1)) : ArchimedeanMatrix F (r + 1)) * colMatrix j w *
        ((Y : ArchimedeanMatrix F (r + 1)) * ((Y⁻¹ : ArchimedeanGL F (r + 1)) :
          ArchimedeanMatrix F (r + 1))) * colMatrix j w * (Y : ArchimedeanMatrix F (r + 1)) := by
        simp only [mul_assoc]
    _ = 0 := by
        rw [h, mul_one, mul_assoc _ (colMatrix j w) (colMatrix j w),
          colMatrix_mul_colMatrix, mul_zero, zero_mul]

theorem isColSupported_infCol {w : Fin (r + 1) → mixedEmbedding.mixedSpace F}
    (hw : IsColSupported j w) : IsColSupported j (infCol F w) := by
  intro a ha
  simp only [infCol, hw a ha, map_zero]
  rfl

/-- The infinite part of the matrix of `colPoint (infCol w)`, in mixed coordinates. -/
theorem archCoord_colPoint_infCol (w : Fin (r + 1) → mixedEmbedding.mixedSpace F) :
    ((archCoord F (colPoint F (j := j) (infCol F w)) : ArchimedeanGL F (r + 1)) :
      ArchimedeanMatrix F (r + 1)) = 1 + colMatrix j w := by
  apply Matrix.ext
  intro a b
  change InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((pointMatrix F (colPoint F (j := j) (infCol F w)) a b).1) = _
  rw [pointMatrix_colPoint, Matrix.add_apply, Matrix.add_apply, colMatrix_apply,
    colMatrix_apply, Matrix.one_apply, Matrix.one_apply, adeles_add_fst, map_add]
  split_ifs
  · rw [infCol]; exact congrArg₂ (· + ·) (map_one _) (RingEquiv.apply_symm_apply _ _)
  · exact congrArg₂ (· + ·) (map_one _) (map_zero _)
  · rw [infCol]; exact congrArg₂ (· + ·) (map_zero _) (RingEquiv.apply_symm_apply _ _)
  · exact congrArg₂ (· + ·) (map_zero _) (map_zero _)

theorem finite_colPoint_infCol (w : Fin (r + 1) → mixedEmbedding.mixedSpace F) :
    AdelicGL.finite F (r + 1)
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (colPoint F (j := j) (infCol F w))) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro a b
  change (pointMatrix F (colPoint F (j := j) (infCol F w)) a b).2 = _
  rw [pointMatrix_colPoint, Matrix.add_apply, colMatrix_apply, Units.val_one, Matrix.one_apply,
    Matrix.one_apply, adeles_add_snd]
  split_ifs
  · exact add_zero _
  · exact add_zero _
  · exact add_zero _
  · exact add_zero _

omit [NumberField F] in
theorem colMatrix_smul (t : ℝ) (w : Fin (r + 1) → mixedEmbedding.mixedSpace F) :
    colMatrix j (t • w) = t • colMatrix j w := by
  refine Matrix.ext fun a b => ?_
  simp only [colMatrix_apply, Matrix.smul_apply, Pi.smul_apply]
  split_ifs <;> simp

/-- **Column translation is an archimedean right translation.**
`(1 + colMatrix(t w)) y = y (1 + t y_∞⁻¹ colMatrix(w) y_∞)`. -/
theorem colPoint_infCol_mul (y : Points F (r + 1))
    (w : Fin (r + 1) → mixedEmbedding.mixedSpace F) (t : ℝ) :
    colPoint F (j := j) (infCol F (t • w)) * y =
      y * archPoint F (r + 1) (t • colConj F j y w)
        (ArchimedeanGL.smul_mul_smul_eq_zero (colConj_mul_self F j y w) t) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [map_mul, map_mul]
  simp only [archPoint, MulEquiv.apply_symm_apply]
  apply AdelicGL.ext_infinite_finite
  · rw [map_mul, map_mul, AdelicGL.infinite_ofInfinite]
    apply (archimedeanGLCoordinates F (r + 1)).injective
    rw [map_mul, map_mul, ArchimedeanGL.squareZeroElement, ContinuousMulEquiv.apply_symm_apply]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ArchimedeanGL.squareZeroUnit_val]
    change ((archCoord F (colPoint F (j := j) (infCol F (t • w))) : ArchimedeanGL F (r + 1)) :
      ArchimedeanMatrix F (r + 1)) * (archCoord F y : ArchimedeanMatrix F (r + 1)) =
      (archCoord F y : ArchimedeanMatrix F (r + 1)) * (1 + t • colConj F j y w)
    rw [archCoord_colPoint_infCol, colMatrix_smul]
    simp only [colConj, mul_add, add_mul, one_mul, mul_one, mul_smul_comm, smul_mul_assoc]
    congr 2
    rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  · rw [map_mul, map_mul, AdelicGL.finite_ofInfinite, finite_colPoint_infCol, one_mul, mul_one]

end Geometry

section Character

/-- The character on a rational combination of an infinite-adelic column. -/
theorem standardCharacter_sum_infCol {r : ℕ} (b : F) (ξ : Fin (r + 1) → F)
    (w : Fin (r + 1) → mixedEmbedding.mixedSpace F) (t : ℝ) :
    EqualAnalytic.standardCharacter F (algebraMap F (Adeles F) b *
        ∑ a, algebraMap F (Adeles F) (ξ a) * infCol F (t • w) a) =
      (𝐞 (t * mixedTrace F (mixedEmbedding F b * ∑ a, mixedEmbedding F (ξ a) * w a)) : ℂ) := by
  have h1 : ∑ a, algebraMap F (Adeles F) (ξ a) * infCol F (t • w) a =
      EqualAnalytic.infiniteAdele F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (t • ∑ a, mixedEmbedding F (ξ a) * w a)) := by
    apply Prod.ext
    · rw [EqualAnalytic.adeles_sum_fst]
      change _ = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (t • ∑ a, mixedEmbedding F (ξ a) * w a)
      apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
      rw [RingEquiv.apply_symm_apply, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, adeles_mul_fst, map_mul,
        adeles_algebraMap_fst]
      change _ * (InfiniteAdeleRing.ringEquiv_mixedSpace F)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((t • w) a)) = _
      rw [RingEquiv.apply_symm_apply, Pi.smul_apply, mul_smul_comm]
    · rw [EqualAnalytic.adeles_sum_snd]
      exact Finset.sum_eq_zero fun a _ => mul_zero _
  rw [h1, EqualAnalytic.standardCharacter_mul_infiniteAdele, RingEquiv.apply_symm_apply,
    mul_smul_comm, map_smul, smul_eq_mul]

/-- `t ↦ 𝐞(t L)` has derivative `2π L i` at `0`. -/
theorem hasDerivAt_fourierChar_mul (L : ℝ) :
    HasDerivAt (fun t : ℝ => ((𝐞 (t * L) : Circle) : ℂ)) (2 * π * L * Complex.I) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => ((2 * π * (t * L) : ℝ) : ℂ)) ((2 * π * L : ℝ) : ℂ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const L).const_mul (2 * π)
    simpa using this.ofReal_comp
  have h2 := (h1.mul_const Complex.I).cexp
  simp only [Real.fourierChar_apply]
  convert h2 using 1
  simp

end Character

section Identity

variable {r : ℕ} {V : Submodule ℂ (Points F (r + 1) → ℂ)}
  {R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V} (hV : WhittakerDecayClass F r V R)
  (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
  {b : F} (hb : ∀ x, ψ x = EqualAnalytic.standardCharacter F (algebraMap F (Adeles F) b * x))

/-- The rational row `(γ_(j,0), …, γ_(j,j), 0, …, 0)` of `γ ∈ GL_(j+1)(F)`, padded. -/
def padRow {j : ℕ} (g0 : RationalGL F (j + 1)) : Fin (r + 1) → F := fun a =>
  if h : (a : ℕ) < j + 1 then (g0 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j) ⟨a, h⟩
  else 0

/-- The real frequency `L = Tr(b Σ_a ξ_a w_a)`. -/
def colFrequency (b : F) (ξ : Fin (r + 1) → F) (w : Fin (r + 1) → mixedEmbedding.mixedSpace F) :
    ℝ :=
  mixedTrace F (mixedEmbedding F b * ∑ a, mixedEmbedding F (ξ a) * w a)

include hV hψ hb

/-- **Character derivative.** Along the archimedean column direction `w`, the derivative of
`W_f` at `diag(γ, I) y` is `2πi L W_f(diag(γ, I) y)`. -/
theorem whittaker_deriv_eq {j : ℕ} (hj : j < r) (g0 : RationalGL F (j + 1)) (f : V)
    (y : Points F (r + 1)) {w : Fin (r + 1) → mixedEmbedding.mixedSpace F}
    (hw : IsColSupported j w) :
    whittaker F r ψ (R (colConj F j y w) f : V)
        (padRational F (by omega : j + 1 ≤ r + 1) g0 * y) =
      (2 * π * colFrequency F b (padRow F g0) w * Complex.I) *
        whittaker F r ψ (f : Points F (r + 1) → ℂ)
          (padRational F (by omega : j + 1 ≤ r + 1) g0 * y) := by
  set Z := colConj F j y w
  have hZ : Z * Z = 0 := colConj_mul_self F j y w
  set g := padRational F (by omega : j + 1 ≤ r + 1) g0 * y
  have hd := hasDerivAt_whittaker F ψ hψ (f : Points F (r + 1) → ℂ)
    ((R Z f : V) : Points F (r + 1) → ℂ) (hV.continuous f) (hV.continuous _)
    (fun k hk x => hV.rational f k hk x) (fun k hk x => hV.rational _ k hk x)
    (hV.bounded f) (hV.bounded _) hZ (hV.deriv f Z hZ) g
  have hfun : (fun t : ℝ => whittaker F r ψ (f : Points F (r + 1) → ℂ)
      (g * archPoint F (r + 1) (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t))) =
      fun t => ((𝐞 (t * colFrequency F b (padRow F g0) w) : Circle) : ℂ) *
        whittaker F r ψ (f : Points F (r + 1) → ℂ) g := by
    funext t
    rw [mul_assoc, ← colPoint_infCol_mul F j y w t,
      whittaker_padRational_colPoint F ψ hψ _ (fun k hk x => hV.rational f k hk x) hj g0 _
        (isColSupported_infCol F j (fun a ha => by rw [Pi.smul_apply, hw a ha, smul_zero])) y,
      hb, colFrequency, ← standardCharacter_sum_infCol]
    congr 3
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [padRow]
    split_ifs <;> simp
  rw [hfun] at hd
  exact hd.unique ((hasDerivAt_fourierChar_mul _).mul_const _)

/-- **Iterated character derivative.** -/
theorem whittaker_pow_deriv_eq {j : ℕ} (hj : j < r) (g0 : RationalGL F (j + 1))
    (y : Points F (r + 1)) {w : Fin (r + 1) → mixedEmbedding.mixedSpace F}
    (hw : IsColSupported j w) (K : ℕ) (f : V) :
    whittaker F r ψ (((R (colConj F j y w)) ^ K) f : V)
        (padRational F (by omega : j + 1 ≤ r + 1) g0 * y) =
      (2 * π * colFrequency F b (padRow F g0) w * Complex.I) ^ K *
        whittaker F r ψ (f : Points F (r + 1) → ℂ)
          (padRational F (by omega : j + 1 ≤ r + 1) g0 * y) := by
  induction K generalizing f with
  | zero => simp
  | succ K ih =>
    rw [pow_succ', Module.End.mul_apply, whittaker_deriv_eq F hV ψ hψ hb hj g0 _ y hw, ih,
      pow_succ', mul_assoc]
    ring

end Identity

end Langlands.Global.RankinSelbergGlobal.Unfolding
