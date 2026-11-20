import Langlands.Analysis.SmoothLinearDeterminant
import Langlands.HarmonicAnalysis.Distribution.SmoothChartVectorField
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! # Differential of the chart Jacobian for a constant coordinate direction -/

noncomputable section

open Filter Function Set TopologicalSpace
open scoped ContDiff Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The derivative of a smooth chart at a point of its source, as an equivalence. -/
def chartFDerivEquiv {e : OpenPartialHomeomorph E X}
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {x : E} (hx : x ∈ e.source) : E ≃L[ℝ] X :=
  ContinuousLinearEquiv.equivOfInverse (fderiv ℝ e x) (fderiv ℝ e.symm (e x))
    (fderiv_chart_symm_apply_fderiv he hei hx)
    (fun v => by
      have h := fderiv_chart_symm_apply_fderiv (e := e.symm) hei he (e.map_source hx) v
      simpa only [e.symm_symm, e.left_inv hx] using h)

/-- Absolute Jacobian of a chart, using a fixed linear identification of the
model and ambient spaces to compare their densities. -/
def chartAbsJacobian (L : E ≃L[ℝ] X) (e : OpenPartialHomeomorph E X) (x : E) : ℝ :=
  |(L.symm.toContinuousLinearMap.comp (fderiv ℝ e x)).det|

variable {e : OpenPartialHomeomorph E X}
  (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
  (L : E ≃L[ℝ] X)

include he hei

theorem chartAbsJacobian_pos {x : E} (hx : x ∈ e.source) :
    0 < chartAbsJacobian L e x := by
  let D := (chartFDerivEquiv he hei hx).trans L.symm
  change 0 < |LinearMap.det D.toLinearMap|
  rw [← LinearEquiv.coe_det]
  exact abs_pos.mpr (Units.ne_zero _)

variable [FiniteDimensional ℝ E]

theorem contDiffOn_chartAbsJacobian :
    ContDiffOn ℝ ∞ (chartAbsJacobian L e) e.source := by
  let C := ContinuousLinearMap.compL ℝ E X E L.symm.toContinuousLinearMap
  have hM : ContDiffOn ℝ ∞ (fun x => (C (fderiv ℝ e x)).det) e.source :=
    Langlands.Analysis.contDiff_continuousLinearMap_det.comp_contDiffOn
      (C.contDiff.comp_contDiffOn (he.fderiv_of_isOpen e.open_source (by simp)))
  exact hM.abs fun x hx => abs_pos.mp (chartAbsJacobian_pos he hei L hx)

theorem fderiv_chartAbsJacobian_apply {x : E} (hx : x ∈ e.source) (u : E) :
    fderiv ℝ (chartAbsJacobian L e) x u = chartAbsJacobian L e x *
      LinearMap.trace ℝ E ((fderiv ℝ e.symm (e x)).comp (fderiv ℝ (fderiv ℝ e) x u)).toLinearMap := by
  let C := ContinuousLinearMap.compL ℝ E X E L.symm.toContinuousLinearMap
  let D := (chartFDerivEquiv he hei hx).trans L.symm
  have hD : D.toContinuousLinearMap = C (fderiv ℝ e x) := rfl
  have hF : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source :=
    he.fderiv_of_isOpen e.open_source (by simp)
  have hdF := ((hF.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hdM := C.hasFDerivAt.comp x hdF
  have hdet := Langlands.Analysis.hasFDerivAt_continuousLinearMap_det D
  rw [hD] at hdet
  have hn : (C (fderiv ℝ e x)).det ≠ 0 := abs_pos.mp (chartAbsJacobian_pos he hei L hx)
  have hdJ := hdet.comp x hdM
  change HasFDerivAt (fun y => (C (fderiv ℝ e y)).det) _ x at hdJ
  have hd := hdJ.abs hn
  change HasFDerivAt (chartAbsJacobian L e) _ x at hd
  rw [hd.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    Langlands.Analysis.continuousEndomorphismTrace_apply, ← mul_assoc]
  have hsign : (SignType.sign (C (fderiv ℝ e x)).det : ℝ) * (C (fderiv ℝ e x)).det =
      chartAbsJacobian L e x := sign_mul_self _
  rw [hsign]
  congr 2
  ext v
  change fderiv ℝ e.symm (e x) (L (L.symm (fderiv ℝ (fderiv ℝ e) x u v))) = _
  rw [L.apply_symm_apply]
  rfl

/-- An ambient expression for a constant coordinate direction in trace-zero
linear fields gives the logarithmic derivative of the chart Jacobian in that
direction. -/
theorem fderiv_chartAbsJacobian_of_linear_fields
    {ι : Type*} [Fintype ι] (A : ι → X →L[ℝ] X)
    (hA : ∀ j, LinearMap.trace ℝ X (A j).toLinearMap = 0)
    {Ω : Opens E} (hΩ : Ω ≤ chartSource e) (u : E) {β : ι → E → ℝ}
    (hβ : ∀ j, ContDiffOn ℝ ∞ (β j) Ω)
    (hu : ∀ x ∈ Ω, fderiv ℝ e x u = ∑ j, β j x • A j (e x))
    {x : E} (hx : x ∈ Ω) :
    fderiv ℝ (chartAbsJacobian L e) x u =
      chartAbsJacobian L e x * ∑ j, fderiv ℝ (β j) x (chartVectorField e (A j) x) := by
  classical
  have hx' : x ∈ e.source := hΩ hx
  rw [fderiv_chartAbsJacobian_apply he hei L hx']
  congr 1
  let K := fderiv ℝ e x
  let I := fderiv ℝ e.symm (e x)
  let H := fderiv ℝ (fderiv ℝ e) x
  let B (j : ι) := fderiv ℝ (β j) x
  have hde : HasFDerivAt e K x :=
    ((he.contDiffAt (e.open_source.mem_nhds hx')).differentiableAt (by simp)).hasFDerivAt
  have hK : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source :=
    he.fderiv_of_isOpen e.open_source (by simp)
  have hdK : HasFDerivAt (fderiv ℝ e) H x := by
    apply DifferentiableAt.hasFDerivAt
    exact (hK.contDiffAt (e.open_source.mem_nhds hx')).differentiableAt (by simp)
  let R (j : ι) : E →L[ℝ] X := β j x • (A j).comp K + (B j).smulRight (A j (e x))
  have hR (j : ι) : HasFDerivAt (fun y => β j y • A j (e y)) (R j) x := by
    have hdB : HasFDerivAt (β j) (B j) x :=
      (((hβ j).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    exact hdB.smul ((A j).hasFDerivAt.comp x hde)
  have hsum : HasFDerivAt (fun y => ∑ j, β j y • A j (e y)) (∑ j, R j) x := by
    have hfun : (∑ j, fun y => β j y • A j (e y)) = fun y => ∑ j, β j y • A j (e y) := by
      funext y
      exact Finset.sum_apply y Finset.univ _
    rw [← hfun]
    exact HasFDerivAt.sum (u := Finset.univ) fun j _ => hR j
  have hlocal : (fun y => fderiv ℝ e y u) =ᶠ[𝓝 x] (fun y => ∑ j, β j y • A j (e y)) := by
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact hu y hy
  have hH := ((ContinuousLinearMap.apply ℝ X u).hasFDerivAt.comp x hdK).unique
    (hsum.congr_of_eventuallyEq hlocal)
  have hH' : H u = ∑ j, R j := by
    ext v
    exact ((he.contDiffAt (e.open_source.mem_nhds hx')).isSymmSndFDerivAt (by simp) u v).trans
      (DFunLike.congr_fun hH v)
  have htrace (j : ι) :
      LinearMap.trace ℝ E (I.comp (R j)).toLinearMap = B j (I (A j (e x))) := by
    let Q := chartFDerivEquiv he hei hx'
    have hcomp : (I.comp (R j)).toLinearMap =
        β j x • Q.symm.toLinearEquiv.conj (A j).toLinearMap +
          (B j).toLinearMap.smulRight (I (A j (e x))) := by
      ext v
      change I (β j x • A j (K v) + B j v • A j (e x)) =
        β j x • I (A j (K v)) + B j v • I (A j (e x))
      simp
    rw [hcomp, map_add, map_smul, LinearMap.trace_conj', hA j, smul_zero, zero_add,
      LinearMap.trace_smulRight]
    rfl
  change LinearMap.trace ℝ E (I.comp (H u)).toLinearMap = _
  rw [hH']
  have hsum' : (I.comp (∑ j, R j)).toLinearMap = ∑ j, (I.comp (R j)).toLinearMap := by
    ext v
    simp
  rw [hsum', map_sum]
  exact Finset.sum_congr rfl fun j _ => htrace j

end Langlands.HarmonicAnalysis
