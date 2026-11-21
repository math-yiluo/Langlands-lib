import Langlands.Analysis.SmoothIntervalParameterIntegral
import Langlands.HarmonicAnalysis.Distribution.ProductTestKernel
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Order.Compact

/-! # Compactly supported primitives in one product coordinate -/

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Opens E} {a b : ℝ}

/-- The open real interval as a test domain. -/
abbrev intervalTestDomain (a b : ℝ) : Opens ℝ := ⟨Ioo a b, isOpen_Ioo⟩

local notation "P" => productTestDomain U (intervalTestDomain a b)

omit [CompleteSpace F] in
/-- Integrate a smooth product test in its interval coordinate. -/
def intervalSliceTest (hab : a ≤ b) (f : 𝓓(P, F)) : 𝓓(U, F) := by
  let h (x : E) := ∫ t in a..b, f (x, t)
  have hK : IsCompact (Prod.fst '' tsupport f) := f.hasCompactSupport.image continuous_fst
  have hs : Function.support h ⊆ Prod.fst '' tsupport f := by
    intro x hx
    by_contra hx'
    have hzero (t : ℝ) : f (x, t) = 0 :=
      image_eq_zero_of_notMem_tsupport fun ht => hx' ⟨(x, t), ht, rfl⟩
    exact hx (by simp [h, hzero])
  refine ⟨h, Langlands.Analysis.contDiff_intervalIntegral_of_joint f.contDiff hab,
    HasCompactSupport.of_support_subset_isCompact hK hs,
    (closure_minimal hs hK.isClosed).trans ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (mem_productTestDomain.mp (f.tsupport_subset hz)).1

omit [CompleteSpace F] in
@[simp]
theorem intervalSliceTest_apply (hab : a ≤ b) (f : 𝓓(P, F)) (x : E) :
    intervalSliceTest hab f x = ∫ t in a..b, f (x, t) := rfl

private theorem exists_inner_interval_of_isCompact_subset_Ioo {S : Set ℝ} (hab : a < b)
    (hS : IsCompact S) (hSub : S ⊆ Ioo a b) :
    ∃ c d : ℝ, a < c ∧ d < b ∧ S ⊆ Ioo c d := by
  by_cases hne : S.Nonempty
  · obtain ⟨mn, hmn⟩ := hS.exists_isLeast hne
    obtain ⟨mx, hmx⟩ := hS.exists_isGreatest hne
    obtain ⟨c, hac, hcmn⟩ := exists_between (hSub hmn.1).1
    obtain ⟨d, hmxd, hdb⟩ := exists_between (hSub hmx.1).2
    exact ⟨c, d, hac, hdb, fun t ht => ⟨hcmn.trans_le (hmn.2 ht), (hmx.2 ht).trans_lt hmxd⟩⟩
  · obtain ⟨c, hac, hcb⟩ := exists_between hab
    exact ⟨c, c, hac, hcb, fun t ht => (hne ⟨t, ht⟩).elim⟩

omit [CompleteSpace F] in
private theorem integral_eq_zero_of_eqOn_uIcc {f : ℝ → F} {c d : ℝ}
    (h : EqOn f 0 (uIcc c d)) : (∫ t in c..d, f t) = 0 :=
  (intervalIntegral.integral_congr h).trans intervalIntegral.integral_zero

omit [CompleteSpace F] in
/-- Integrate a test of zero slice integral from the left endpoint to the interval
coordinate. The result has compact support and is a primitive for complete `F`. -/
def intervalPrimitiveTest (hab : a < b) (f : 𝓓(P, F))
    (hf : intervalSliceTest hab.le f = 0) : 𝓓(P, F) := by
  let H (z : E × ℝ) := ∫ t in a..z.2, f (z.1, t)
  let K := Prod.fst '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_fst
  have hS : IsCompact (Prod.snd '' tsupport f) := f.hasCompactSupport.image continuous_snd
  have hsub : Prod.snd '' tsupport f ⊆ Ioo a b := by
    rintro _ ⟨z, hz, rfl⟩
    exact (mem_productTestDomain.mp (f.tsupport_subset hz)).2
  have he := exists_inner_interval_of_isCompact_subset_Ioo hab hS hsub
  let c := he.choose
  let d := he.choose_spec.choose
  have hac : a < c := he.choose_spec.choose_spec.1
  have hdb : d < b := he.choose_spec.choose_spec.2.1
  have hcd : Prod.snd '' tsupport f ⊆ Ioo c d := he.choose_spec.choose_spec.2.2
  have hs : Function.support H ⊆ K ×ˢ Icc c d := by
    rintro ⟨x, t⟩ hxt
    have hzero_t (s : ℝ) (hs : s ∉ Ioo c d) : f (x, s) = 0 :=
      image_eq_zero_of_notMem_tsupport fun hfs => hs (hcd ⟨(x, s), hfs, rfl⟩)
    constructor
    · by_contra hx
      have hzero (s : ℝ) : f (x, s) = 0 :=
        image_eq_zero_of_notMem_tsupport fun hfs => hx ⟨(x, s), hfs, rfl⟩
      exact hxt (by simp [H, hzero])
    · refine ⟨?_, ?_⟩
      · by_contra! ht
        apply hxt
        apply integral_eq_zero_of_eqOn_uIcc
        intro s hs
        exact hzero_t s fun hsc => (hs.2.trans_lt (max_lt hac ht)).not_gt hsc.1
      · by_contra! ht
        apply hxt
        have hz : (∫ s in b..t, f (x, s)) = 0 := by
          apply integral_eq_zero_of_eqOn_uIcc
          intro s hs
          exact hzero_t s fun hsd => (lt_of_lt_of_le (lt_min hdb ht) hs.1).not_gt hsd.2
        have hi : Continuous (fun s => f (x, s)) :=
          f.continuous.comp (continuous_const.prodMk continuous_id)
        have hsum := intervalIntegral.integral_add_adjacent_intervals
          (hi.intervalIntegrable (μ := volume) a b) (hi.intervalIntegrable (μ := volume) b t)
        rw [hz, add_zero] at hsum
        exact hsum.symm.trans (congrArg (fun g : 𝓓(U, F) => g x) hf)
  have hH : ContDiff ℝ ∞ H :=
    (Langlands.Analysis.contDiff_intervalIntegral_to_variable
      (f.contDiff.comp (contDiff_snd.prodMk contDiff_fst)) a).comp
      (contDiff_snd.prodMk contDiff_fst)
  have hprod : IsCompact (K ×ˢ Icc c d) := hK.prod isCompact_Icc
  refine ⟨H, hH, HasCompactSupport.of_support_subset_isCompact hprod hs,
    (closure_minimal hs hprod.isClosed).trans ?_⟩
  rintro ⟨x, t⟩ ⟨⟨z, hz, rfl⟩, ht⟩
  exact mem_productTestDomain.mpr
    ⟨(mem_productTestDomain.mp (f.tsupport_subset hz)).1,
      ⟨hac.trans_le ht.1, ht.2.trans_lt hdb⟩⟩

omit [CompleteSpace F] in
@[simp]
theorem intervalPrimitiveTest_apply (hab : a < b) (f : 𝓓(P, F))
    (hf : intervalSliceTest hab.le f = 0) (z : E × ℝ) :
    intervalPrimitiveTest hab f hf z = ∫ t in a..z.2, f (z.1, t) := rfl

theorem lineDeriv_intervalPrimitiveTest (hab : a < b) (f : 𝓓(P, F))
    (hf : intervalSliceTest hab.le f = 0) :
    (TestFunction.lineDerivCLM ℝ (0, 1) (intervalPrimitiveTest hab f hf) : 𝓓(P, F)) = f := by
  let g := intervalPrimitiveTest hab f hf
  ext1 z
  have hd := (g.contDiff.differentiable (by simp)).differentiableAt (x := z)
  rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le _ le_top]
  change fderiv ℝ g z (0, 1) = f z
  have hcurve : HasDerivAt (fun t : ℝ => (z.1, t)) (0, 1) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have hg := (hd.hasFDerivAt.comp_hasDerivAt z.2 hcurve).deriv
  have heq : (⇑g ∘ fun t : ℝ => (z.1, t)) = fun t => ∫ s in a..t, f (z.1, s) :=
    funext fun t => intervalPrimitiveTest_apply hab f hf (z.1, t)
  rw [heq] at hg
  have hcont : Continuous (fun t => f (z.1, t)) :=
    f.continuous.comp (continuous_const.prodMk continuous_id)
  have hp := intervalIntegral.deriv_integral_right (hcont.intervalIntegrable a z.2)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  exact hg.symm.trans hp

omit [CompleteSpace F] in
/-- Extend a parameter test with a fixed scalar test in the interval variable. -/
def intervalProductTestCLM (χ : 𝓓(intervalTestDomain a b, ℝ)) : 𝓓(U, F) →L[ℝ] 𝓓(P, F) :=
  productKernelTestCLM (TestFunction.postcompCLM
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℝ F)) χ)

omit [CompleteSpace F] in
@[simp]
theorem intervalProductTestCLM_apply (χ : 𝓓(intervalTestDomain a b, ℝ)) (f : 𝓓(U, F))
    (z : E × ℝ) : intervalProductTestCLM χ f z = χ z.2 • f z.1 := rfl

/-- A continuous functional that annihilates interval derivatives factors
through integration in the interval coordinate. -/
theorem eval_eq_of_annihilates_intervalDerivatives (hab : a < b)
    (T : 𝓓(P, F) →L[ℝ] G)
    (hT : ∀ f : 𝓓(P, F), T (TestFunction.lineDerivCLM ℝ (0, 1) f) = 0)
    (χ : 𝓓(intervalTestDomain a b, ℝ)) (hχ : (∫ t in a..b, χ t) = 1)
    (f : 𝓓(P, F)) : T f = (T.comp (intervalProductTestCLM χ)) (intervalSliceTest hab.le f) := by
  let q := intervalProductTestCLM χ (intervalSliceTest hab.le f)
  have h0 : intervalSliceTest hab.le (f - q) = 0 := by
    ext x
    rw [intervalSliceTest_apply]
    have hslice (g : 𝓓(P, F)) : Continuous (fun t => g (x, t)) :=
      g.continuous.comp (continuous_const.prodMk continuous_id)
    change (∫ t in a..b, f (x, t) - q (x, t)) = 0
    rw [intervalIntegral.integral_sub ((hslice f).intervalIntegrable a b)
      ((hslice q).intervalIntegrable a b)]
    simp only [q, intervalProductTestCLM_apply, intervalIntegral.integral_smul_const,
      hχ, one_smul, intervalSliceTest_apply, sub_self]
  have hz := hT (intervalPrimitiveTest hab (f - q) h0)
  rw [lineDeriv_intervalPrimitiveTest, map_sub] at hz
  exact sub_eq_zero.mp hz

end Langlands.HarmonicAnalysis
