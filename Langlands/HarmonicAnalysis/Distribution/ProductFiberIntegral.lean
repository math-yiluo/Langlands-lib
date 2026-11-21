import Langlands.Analysis.SmoothIntervalParameterIntegral
import Langlands.HarmonicAnalysis.Distribution.ProductTestKernel
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! # Smooth integration of a product test in one of its factors -/

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E W F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace W] [BorelSpace W]
  {U : Opens E} {V : Opens W}
  (μ : Measure W) [IsLocallyFiniteMeasure μ]

private theorem smooth_setIntegral_and_iteratedFDeriv_of_joint
    {K : Set W} (hK : IsCompact K) {h : E × W → F} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun x => ∫ y in K, h (x, y) ∂μ) ∧
    ∀ (i : ℕ) (x : E) (v : Fin i → E),
      iteratedFDeriv ℝ i (fun x => ∫ y in K, h (x, y) ∂μ) x v =
        ∫ y in K, iteratedFDeriv ℝ i (fun z => h (z, y)) x v ∂μ := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ν : Measure K := μ.comap Subtype.val
  have hm := hK.isClosed.measurableSet
  let _ : IsFiniteMeasure ν := ⟨by
    change μ.comap (Subtype.val : K → W) univ < ⊤
    rw [Measure.comap_apply _ Subtype.val_injective
      (fun s hs => (MeasurableEmbedding.subtype_coe hm).measurableSet_image' hs) _ MeasurableSet.univ,
      image_univ, Subtype.range_coe]
    exact hK.measure_lt_top⟩
  let j : C(K, W) := ⟨Subtype.val, continuous_subtype_val⟩
  let H (x : E) : C(K, F) :=
    ⟨fun y => h (x, y.val), hh.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩
  have hH : ContDiff ℝ ∞ H := by
    apply contDiffOn_univ.mp
    exact Langlands.Analysis.contDiffOn_infty_compactFamily_of_joint (f := H) j
      isOpen_univ isOpen_univ (fun _ => mem_univ _) hh.contDiffOn (fun _ _ _ => rfl)
  let I := Langlands.Analysis.compactContinuousIntegralCLM (F := F) ν
  have heq : (fun x => ∫ y in K, h (x, y) ∂μ) = I ∘ H := by
    funext x
    exact (integral_subtype_comap hm (fun y => h (x, y))).symm
  rw [heq]
  refine ⟨I.contDiff.comp hH, fun i x v => ?_⟩
  rw [I.iteratedFDeriv_comp_left hH.contDiffAt (by simp)]
  change (∫ y : K, (iteratedFDeriv ℝ i H x v) y ∂ν) =
    ∫ y in K, iteratedFDeriv ℝ i (fun z => h (z, y)) x v ∂μ
  rw [← integral_subtype_comap hm]
  congr 1
  funext y
  let ev : C(K, F) →L[ℝ] F := ContinuousMap.evalCLM ℝ y
  have hD := ev.iteratedFDeriv_comp_left (i := i) (x := x) hH.contDiffAt (by simp)
  exact (DFunLike.congr_fun hD v).symm

omit [BorelSpace W] [IsLocallyFiniteMeasure μ] in
private theorem integral_product_slice_eq_setIntegral (f : 𝓓(productTestDomain U V, F)) (x : E) :
    (∫ y, f (x, y) ∂μ) = ∫ y in Prod.snd '' tsupport f, f (x, y) ∂μ := by
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
    image_eq_zero_of_notMem_tsupport ?_
  exact fun hs => hy ⟨(x, y), hs, rfl⟩

/-- Integrate the second variable of a smooth compactly supported product test. -/
def productFiberIntegralTest (f : 𝓓(productTestDomain U V, F)) : 𝓓(U, F) := by
  let g (x : E) := ∫ y, f (x, y) ∂μ
  have hK := f.hasCompactSupport.image continuous_snd
  have hg : ContDiff ℝ ∞ g := by
    have heq : g = fun x => ∫ y in Prod.snd '' tsupport f, f (x, y) ∂μ :=
      funext (integral_product_slice_eq_setIntegral μ f)
    rw [heq]
    exact (smooth_setIntegral_and_iteratedFDeriv_of_joint μ hK f.contDiff).1
  have hL := f.hasCompactSupport.image continuous_fst
  have hs : Function.support g ⊆ Prod.fst '' tsupport f := by
    intro x hx
    by_contra hn
    apply hx
    have hzero (y : W) : f (x, y) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hs => hn ⟨(x, y), hs, rfl⟩)
    simp [g, hzero]
  refine ⟨g, hg, HasCompactSupport.of_support_subset_isCompact hL hs,
    (closure_minimal hs hL.isClosed).trans ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact (mem_productTestDomain.mp (f.tsupport_subset hp)).1

@[simp]
theorem productFiberIntegralTest_apply (f : 𝓓(productTestDomain U V, F)) (x : E) :
    productFiberIntegralTest μ f x = ∫ y, f (x, y) ∂μ := rfl

/-- All derivatives in the first variable commute with the fiber integral. -/
theorem iteratedFDeriv_productFiberIntegralTest_apply
    (f : 𝓓(productTestDomain U V, F)) (i : ℕ) (x : E) (v : Fin i → E) :
    iteratedFDeriv ℝ i (productFiberIntegralTest μ f) x v =
      ∫ y, iteratedFDeriv ℝ i (fun z => f (z, y)) x v ∂μ := by
  have heq : (productFiberIntegralTest μ f : E → F) =
      fun x => ∫ y in Prod.snd '' tsupport f, f (x, y) ∂μ :=
    funext (integral_product_slice_eq_setIntegral μ f)
  rw [heq, (smooth_setIntegral_and_iteratedFDeriv_of_joint μ
    (f.hasCompactSupport.image continuous_snd) f.contDiff).2]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  have hzero : (fun z => f (z, y)) = 0 :=
    funext fun z => image_eq_zero_of_notMem_tsupport (fun hs => hy ⟨(z, y), hs, rfl⟩)
  simp [hzero]

/-- A neighborhood of a point contains a nonnegative smooth test of integral one. -/
theorem exists_normalized_smoothTest [FiniteDimensional ℝ W] [μ.IsOpenPosMeasure]
    {x : W} (hx : x ∈ V) :
    ∃ χ : 𝓓(V, ℝ), (∀ y, 0 ≤ χ y) ∧ (∫ y, χ y ∂μ) = 1 := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (V.isOpen.mem_nhds hx)
  let b : ContDiffBump x := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let χ : 𝓓(V, ℝ) :=
    ⟨b.normed μ, b.contDiff_normed, b.hasCompactSupport_normed,
      b.tsupport_normed_eq (μ := μ) ▸ hball⟩
  exact ⟨χ, b.nonneg_normed, b.integral_normed⟩

end Langlands.HarmonicAnalysis
