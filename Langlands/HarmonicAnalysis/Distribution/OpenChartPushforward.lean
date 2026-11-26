import Langlands.HarmonicAnalysis.Distribution.TestPushforward
import Langlands.HarmonicAnalysis.Distribution.Subspace

/-! # Pushforward in open charts with locally constant measure weights -/

noncomputable section

namespace Langlands.HarmonicAnalysis.SchwartzBruhat

open MeasureTheory Set Function _root_.Topology
open Hecke.TestFunction (characteristic characteristic_apply isCompact_support pullback pullback_apply)
open scoped ENNReal NNReal

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [BorelSpace X] [BorelSpace Y]
  [BorelSpace Z]

section Support

variable [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
  {p : X → Y} {P : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y}

omit [BorelSpace X] in
/-- Pushforward tests are supported in the compact image of the support. -/
theorem IsTestPushforward.support_apply_subset (hP : IsTestPushforward μ ν p P)
    (hp : Continuous p) (f : SchwartzBruhat X) :
    support (P f : Y → ℂ) ⊆ p '' support (f : X → ℂ) := by
  intro y hy
  by_contra hnot
  have hClosed := ((isCompact_support f).image hp).isClosed
  have hn : (p '' support (f : X → ℂ))ᶜ ∩ {z : Y | P f z = P f y} ∈ nhds y :=
    Filter.inter_mem (hClosed.isOpen_compl.mem_nhds hnot) ((P f).locallyConstant.eventually_eq y)
  obtain ⟨U, hUc, hU, hyU, hsub⟩ := Langlands.HarmonicAnalysis.exists_compact_clopen hn
  let g := characteristic hU hUc
  have hzero : (∫ x, f x * g (p x) ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : f x = 0
      · simp [hx]
      · have hpx : p x ∉ U := fun h => (hsub h).1 ⟨x, hx, rfl⟩
        simp [g, characteristic_apply, hpx]
  have hvalue : (∫ z, P f z * g z ∂ν) = P f y * Distribution.ofMeasure ν g := by
    rw [Distribution.ofMeasure_apply, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      change P f z * g z = P f y * g z
      by_cases hz : z ∈ U
      · rw [(hsub hz).2]
      · simp [g, characteristic_apply, hz]
  exact (mul_ne_zero hy (Distribution.RenardHaar.ofMeasure_characteristic_ne_zero ν hU hUc
    ⟨y, hyU⟩)) (hvalue.symm.trans ((hP f g).trans hzero))

/-- Restrict a test to an embedded subspace when its support lies in the image. -/
private def pullbackSupported {j : Z → Y} (hj : IsEmbedding j) (f : SchwartzBruhat Y)
    (hf : support (f : Y → ℂ) ⊆ range j) : SchwartzBruhat Z := by
  let := hj.t2Space
  exact ⟨f ∘ j, f.locallyConstant.comp_continuous hj.continuous,
    HasCompactSupport.of_support_subset_isCompact
      (K := j ⁻¹' support (f : Y → ℂ))
      (hj.isCompact_iff.2 (by
        rw [image_preimage_eq_inter_range, inter_eq_left.mpr hf]
        exact isCompact_support f))
      (by rfl)⟩

omit [BorelSpace X] in
/-- An output chart containing the image of a map carries its test pushforward
with the measure pulled back from the ambient space. -/
theorem IsTestPushforward.exists_openTarget {j : Z → Y} (hj : IsOpenEmbedding j)
    {q : X → Z} (hq : Continuous q) (hP : IsTestPushforward μ ν (j ∘ q) P) :
    ∃ Q : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Z, IsTestPushforward μ (ν.comap j) q Q := by
  let e := hj.isEmbedding.toHomeomorph
  have hS (f : SchwartzBruhat X) : support (P f : Y → ℂ) ⊆ range j :=
    (hP.support_apply_subset (hj.continuous.comp hq) f).trans (by
      rintro _ ⟨x, _, rfl⟩
      exact ⟨q x, rfl⟩)
  let Q : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Z := {
    toFun f := pullbackSupported hj.isEmbedding (P f) (hS f)
    map_add' f g := by
      ext z
      change P (f + g) (j z) = P f (j z) + P g (j z)
      rw [map_add]
      rfl
    map_smul' a f := by
      ext z
      change P (a • f) (j z) = a • P f (j z)
      rw [map_smul]
      rfl }
  refine ⟨Q, fun f g => ?_⟩
  let g' := extendZero hj.isOpen_range (Hecke.TestFunction.pullback e.symm g)
  have hg (z : Z) : g' (j z) = g z := by
    change SchwartzBruhat.extendZero hj.isOpen_range (Hecke.TestFunction.pullback e.symm g) (e z).val = g z
    rw [extendZero_apply_subtype, pullback_apply, e.symm_apply_apply]
  have hg0 (y : Y) (hy : y ∉ range j) : g' y = 0 :=
    extendZero_apply_of_not_mem _ _ hy
  have hf := hP f g'
  change (∫ y, P f y * g' y ∂ν) = ∫ x, f x * g' (j (q x)) ∂μ at hf
  simp_rw [hg] at hf
  rw [← hf]
  have he := hj.measurableEmbedding
  calc
    _ = ∫ y in range j, P f y * g' y ∂ν := by
      rw [← he.map_comap, he.integral_map]
      simp only [hg]
      rfl
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by simp [hg0 y hy])

end Support

section Weights

variable {μ : Measure X} {ν : Measure Y} {p : X → Y}
  {P : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y}
  (hP : IsTestPushforward μ ν p P)

private def complexWeight {A : Type*} [TopologicalSpace A] (w : LocallyConstant A ℝ≥0) :
    LocallyConstant A ℂ := LocallyConstant.map (fun r : ℝ≥0 => ((r : ℝ) : ℂ)) w

include hP in
/-- Locally constant source and positive target weights can be absorbed into
multipliers of the source and target test functions. -/
theorem IsTestPushforward.exists_weighted (w : LocallyConstant X ℝ≥0)
    (v : LocallyConstant Y ℝ≥0) (hv : ∀ y, v y ≠ 0) :
    ∃ Q : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y,
      IsTestPushforward (μ.withDensity (fun x => (w x : ℝ≥0∞)))
        (ν.withDensity (fun y => (v y : ℝ≥0∞))) p Q := by
  let vInv := LocallyConstant.map (fun z : ℂ => z⁻¹) (complexWeight v)
  let Q := (Distribution.multiplyTest vInv).comp (P.comp (Distribution.multiplyTest (complexWeight w)))
  refine ⟨Q, fun f g => ?_⟩
  rw [integral_withDensity_eq_integral_smul v.continuous.measurable,
    integral_withDensity_eq_integral_smul w.continuous.measurable]
  let f' := Distribution.multiplyTest (complexWeight w) f
  have hv' (y : Y) : complexWeight v y ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (by exact_mod_cast hv y)
  have hQ (y : Y) : Q f y = (complexWeight v y)⁻¹ * P f' y := rfl
  have hL : (fun y : Y => v y • (Q f y * g y)) = fun y => P f' y * g y := by
    funext y
    rw [NNReal.smul_def, Complex.real_smul, hQ]
    change complexWeight v y * ((complexWeight v y)⁻¹ * P f' y * g y) = _
    simp only [← mul_assoc, mul_inv_cancel₀ (hv' y), one_mul]
  have hR : (fun x : X => w x • (f x * g (p x))) = fun x => f' x * g (p x) := by
    funext x
    rw [NNReal.smul_def, Complex.real_smul, ← mul_assoc]
    rfl
  rw [hL, hR]
  exact hP f' g

end Weights

end Langlands.HarmonicAnalysis.SchwartzBruhat
