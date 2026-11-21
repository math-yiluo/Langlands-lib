import Langlands.Analysis.SmoothChartVectorFields
import Langlands.Group.GL.BruhatCellMatrixSlice
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Linear

/-! # Tangent matrix fields in a local Bruhat chart -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Filter
open scoped ContDiff Matrix.Norms.Operator Topology

namespace Langlands.GeneralLinear

universe u v

variable {F : Type u} [RCLike F] {n : ℕ} (w : Equiv.Perm (Fin n))

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "B" => upperTriangularSubgroup n F
local notation "V" => permutationUnipotentMinus n F w
local notation "P" => permutation n F w
local notation "T" => (bruhatUpperSpace F n × bruhatInversionSpace F w)

private theorem exists_bruhatTangentCurve {x : M} (hx : x ∈ bruhatCellMatrixSet F w)
    (X : M) (hX : ∀ b : B, ∀ i j, bruhatNormalEntry w i j →
      ((b⁻¹ : B).val.val * X * b.val.val) i j = 0) :
    ∃ c : ℝ → M, c 0 = x ∧ HasDerivAt c (X * x) 0 ∧
      ∀ᶠ t in 𝓝 0, c t ∈ bruhatCellMatrixSet F w := by
  obtain ⟨g, hg⟩ := hx
  let e := UpperBruhatCoordinates.cellHomeomorph (K := F) w
  let q : B × V := e.symm g
  let b := q.1
  let v := q.2
  let p := P * v.val
  obtain ⟨s, hs⟩ := exists_bruhatTangentCoordinates w
    ((b⁻¹ : B).val.val * X * b.val.val) (hX b)
  have hb : b.val.val * p.val = x := by
    have he := congrArg (fun a : UpperBruhatCell n F w => a.val.val) (e.apply_symm_apply g)
    change (b.val * P * v.val).val = g.val.val at he
    rw [mul_assoc] at he
    exact he.trans hg
  let line : ℝ →L[ℝ] T := ContinuousLinearMap.toSpanSingleton ℝ s
  let f := bruhatCellMatrixParam (w := w) b p
  have hline : HasDerivAt line s 0 := by
    have h := line.hasDerivAt (x := (0 : ℝ))
    simpa only [line, ContinuousLinearMap.toSpanSingleton_apply, one_smul] using h
  have hd : HasFDerivAt f (bruhatCellMatrixDifferential (w := w) b p) (line 0) := by
    rw [map_zero]
    exact hasFDerivAt_bruhatCellMatrixParam (w := w) b p
  have hderiv := hd.comp_hasDerivAt 0 hline
  have hdX : bruhatCellMatrixDifferential (w := w) b p s = X * x := by
    rw [bruhatCellMatrixDifferential_apply, ← hs, ← hb]
    have hbi : b.val.val * (b⁻¹ : B).val.val = 1 := b.val.val_inv
    simp only [← mul_assoc, hbi, one_mul]
  rw [hdX] at hderiv
  refine ⟨f ∘ line, ?_, hderiv, ?_⟩
  · simp only [Function.comp_apply, map_zero, f, bruhatCellMatrixParam_zero, hb]
  · have hcont : Tendsto line (𝓝 0) (𝓝 (0 : T)) := by
      have h : Tendsto line (𝓝 0) (𝓝 (line 0)) := line.continuous.continuousAt
      rwa [map_zero] at h
    exact hcont.eventually (eventually_bruhatCellMatrixParam_mem w b v)

/-- Pulling back a field whose conjugate has zero normal entries gives
zero normal velocity at each point of a local zero slice. -/
theorem bruhatChart_normal_derivative_eq_zero {Y : Type v}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : OpenPartialHomeomorph (T × Y) M) {z : T × Y} (hz : z ∈ e.source)
    (hcell : ∀ᶠ q in 𝓝 z, e q ∈ bruhatCellMatrixSet F w → q.2 = 0)
    (hzcell : e z ∈ bruhatCellMatrixSet F w) (hDiff : DifferentiableAt ℝ e.symm (e z))
    (X : M) (hX : ∀ b : B, ∀ i j, bruhatNormalEntry w i j →
      ((b⁻¹ : B).val.val * X * b.val.val) i j = 0) :
    (fderiv ℝ e.symm (e z) (X * e z)).2 = 0 := by
  obtain ⟨c, hc₀, hc', hccell⟩ := exists_bruhatTangentCurve w hzcell X hX
  have ht : e z ∈ e.target := e.map_source hz
  have hct : Tendsto c (𝓝 0) (𝓝 (e z)) := hc₀ ▸ hc'.continuousAt
  have hinv : Tendsto e.symm (𝓝 (e z)) (𝓝 z) := by
    have h : Tendsto e.symm (𝓝 (e z)) (𝓝 (e.symm (e z))) := e.symm.continuousAt ht
    rwa [e.left_inv hz] at h
  have hs : (fun t : ℝ => (e.symm (c t)).2) =ᶠ[𝓝 0] (fun _ => 0 : ℝ → Y) := by
    filter_upwards [hccell, hct.eventually (e.open_target.mem_nhds ht),
      (hinv.comp hct).eventually hcell] with t htc htt hq
    apply hq
    change e (e.symm (c t)) ∈ bruhatCellMatrixSet F w
    rwa [e.right_inv htt]
  have hder := hDiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc' hc₀.symm
  let π := ContinuousLinearMap.snd ℝ T Y
  have hπ : HasFDerivAt π π ((e.symm ∘ c) 0) := π.hasFDerivAt
  have hd := hπ.comp_hasDerivAt 0 hder
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : Y)).congr_of_eventuallyEq hs)

/-- If the chart identifies the actual cell with the zero slice, a
field with zero normal entries after upper conjugation is tangent there. -/
theorem bruhatChart_tangent_of_cellSlice {Y : Type v}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : OpenPartialHomeomorph (T × Y) M) (hs : ContDiffOn ℝ ∞ e.symm e.target)
    (hCell : ∀ z ∈ e.source, e z ∈ bruhatCellMatrixSet F w ↔ z.2 = 0)
    (A : M) (hA : ∀ b : B, ∀ i j, bruhatNormalEntry w i j →
      ((b⁻¹ : B).val.val * A * b.val.val) i j = 0)
    (x : T) (hx : (x, (0 : Y)) ∈ e.source) :
    (Langlands.HarmonicAnalysis.chartVectorField e (fun z => A * z) (x, (0 : Y))).2 = 0 := by
  change (fderiv ℝ e.symm (e (x, 0)) (A * e (x, 0))).2 = 0
  apply bruhatChart_normal_derivative_eq_zero w e hx
  · filter_upwards [e.open_source.mem_nhds hx] with z hz using (hCell z hz).mp
  · exact (hCell _ hx).mpr rfl
  · exact (hs.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)
  · exact hA

end Langlands.GeneralLinear
