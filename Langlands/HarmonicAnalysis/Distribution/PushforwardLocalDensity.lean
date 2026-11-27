import Langlands.HarmonicAnalysis.Distribution.TestPushforward
import Langlands.HarmonicAnalysis.Distribution.IntegrablePushforward
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Local densities detected by pushforward of tests -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open MeasureTheory Function Set TopologicalSpace _root_.Topology
open Hecke.TestFunction (characteristic characteristic_apply)
open scoped ENNReal NNReal

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [borelX : BorelSpace X] [MeasurableSpace Y] [borelY : BorelSpace Y]
  {μ : Measure X} {ν : Measure Y}
  {p : X → Y} {P : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y}

private theorem indicator_pushforward_test (hp : Continuous p)
    (hP : SchwartzBruhat.IsTestPushforward μ ν p P) {K : Set X}
    (hK : IsClopen K) (hKc : IsCompact K) (g : SchwartzBruhat Y) :
    (∫ y, P (characteristic hK hKc) y * g y ∂ν) = ∫ y, g y ∂((μ.restrict K).map p) := by
  rw [hP, integral_map hp.measurable.aemeasurable g.continuous.measurable.aestronglyMeasurable,
    ← integral_indicator hK.2.measurableSet]
  congr 1
  funext x
  by_cases hx : x ∈ K <;> simp [characteristic_apply, hx]

private theorem indicator_pushforward_mul_measure (hp : Continuous p)
    (hP : SchwartzBruhat.IsTestPushforward μ ν p P) {K : Set X} (hK : IsClopen K) (hKc : IsCompact K)
    {V : Set Y} (hV : IsClopen V) (hVc : IsCompact V) {a : ℂ}
    (hc : ∀ y ∈ V, P (characteristic hK hKc) y = a) :
    (ν.real V : ℂ) * a = ((μ.restrict K).map p).real V := by
  have hpoint : (fun y => P (characteristic hK hKc) y * characteristic hV hVc y) =
      V.indicator (fun _ => a) := by
    funext y
    by_cases hy : y ∈ V <;> simp [characteristic_apply, hy, hc]
  have h := indicator_pushforward_test hp hP hK hKc (characteristic hV hVc)
  rw [hpoint, integral_indicator_const a hV.2.measurableSet] at h
  simp only [characteristic_apply, integral_indicator_const (1 : ℂ) hV.2.measurableSet,
    Complex.real_smul, mul_one] at h
  exact h

variable [hausdorffY : T2Space Y] [compactY : LocallyCompactSpace Y]
  [disconnectedY : TotallyDisconnectedSpace Y] [countableY : SecondCountableTopology Y]
  [IsFiniteMeasureOnCompacts μ]
  [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]

/-- The pushforward of the source measure restricted to a compact clopen set has
 the nonnegative locally constant density given by pushforward of its characteristic test. -/
theorem SchwartzBruhat.IsTestPushforward.exists_compactClopenDensity
    (hP : SchwartzBruhat.IsTestPushforward μ ν p P) (hp : Continuous p) {K : Set X}
    (hK : IsClopen K) (hKc : IsCompact K) :
    ∃ r : LocallyConstant Y ℝ≥0, (∀ y, P (characteristic hK hKc) y = (r y : ℝ)) ∧
      (μ.restrict K).map p = ν.withDensity (fun y => (r y : ℝ≥0∞)) := by
  let f := P (characteristic hK hKc)
  let m := (μ.restrict K).map p
  have hreim (y : Y) : 0 ≤ (f y).re ∧ (f y).im = 0 := by
    obtain ⟨V, hVc, hV, hyV, hVf⟩ := exists_compact_clopen (f.locallyConstant.eventually_eq y)
    have h := indicator_pushforward_mul_measure hp hP hK hKc hV hVc hVf
    have hpos : 0 < ν.real V := ENNReal.toReal_pos (hV.2.measure_pos ν ⟨y, hyV⟩).ne' hVc.measure_ne_top
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hi
    exact ⟨nonneg_of_mul_nonneg_right (hr.symm ▸ ENNReal.toReal_nonneg) hpos,
      (mul_eq_zero.mp hi).resolve_left hpos.ne'⟩
  let r : LocallyConstant Y ℝ≥0 :=
    ⟨fun y => ⟨(f y).re, (hreim y).1⟩,
      (IsLocallyConstant.iff_eventually_eq _).2 fun y =>
        (f.locallyConstant.eventually_eq y).mono fun _ h => Subtype.ext (congrArg Complex.re h)⟩
  have hr (y : Y) : f y = (r y : ℝ) := Complex.ext rfl (by simpa using (hreim y).2)
  refine ⟨r, hr, ?_⟩
  let m' := ν.withDensity (fun y => (r y : ℝ≥0∞))
  have hm : IsFiniteMeasure m := by
    have : IsFiniteMeasure (μ.restrict K) := ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
      exact hKc.measure_lt_top⟩
    dsimp [m]
    infer_instance
  have hm' : IsFiniteMeasure m' := by
    have hf := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport (μ := ν)
    have hfin : IsFiniteMeasure (ν.withDensity (fun y => ENNReal.ofReal (f y).re)) :=
      isFiniteMeasure_withDensity_ofReal hf.re.hasFiniteIntegral
    convert hfin using 1
    change (ν.withDensity (fun y => (r y : ℝ≥0∞))) = _
    congr 1
    funext y
    exact (ENNReal.ofReal_coe_nnreal (p := r y)).symm
  let C : Set (Set Y) := {V | IsCompact V ∧ IsClopen V}
  have hC : IsTopologicalBasis C := isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.2.2)
    (fun _ _ hv ho => by
      obtain ⟨V, hVc, hV, hxV, hsub⟩ := exists_compact_clopen (ho.mem_nhds hv)
      exact ⟨V, ⟨hVc, hV⟩, hxV, hsub⟩)
  have hπ : IsPiSystem C := fun _ hs _ ht _ => ⟨hs.1.inter_right ht.2.1, hs.2.inter ht.2⟩
  obtain ⟨A, hAC, hA, hcover⟩ := hC.exists_countable_biUnion_of_isOpen (isOpen_univ (X := Y))
  change m = m'
  refine Measure.ext_of_generateFrom_of_cover_subset
    ((BorelSpace.measurable_eq (α := Y)).trans hC.borel_eq_generateFrom) hπ hAC hA
    (by rw [sUnion_eq_biUnion, ← hcover]) (fun V _ => measure_ne_top m V) ?_
  intro V hV
  let g := characteristic hV.2 hV.1
  have hi := indicator_pushforward_test hp hP hK hKc g
  have hi' : (∫ y, f y * g y ∂ν) = ∫ y, g y ∂m' := by
    rw [integral_withDensity_eq_integral_smul r.continuous.measurable]
    simp_rw [hr, NNReal.smul_def, Complex.real_smul]
  have h := hi.symm.trans hi'
  change (∫ y, V.indicator (fun _ => (1 : ℂ)) y ∂m) =
    ∫ y, V.indicator (fun _ => (1 : ℂ)) y ∂m' at h
  simp only [integral_indicator_const (1 : ℂ) hV.2.2.measurableSet, Complex.real_smul,
    mul_one] at h
  have h' : (m V).toReal = (m' V).toReal := by simpa [Measure.real] using congrArg Complex.re h
  exact ENNReal.toReal_eq_toReal_iff' (measure_ne_top m _) (measure_ne_top m' _) |>.mp h'

private def cutoffPullback [T2Space X] (hp : Continuous p) {K : Set X}
    (hK : IsClopen K) (hKc : IsCompact K) (g : SchwartzBruhat Y) : SchwartzBruhat X :=
  ⟨fun x => characteristic hK hKc x * g (p x),
    (characteristic hK hKc).locallyConstant.mul (g.locallyConstant.comp_continuous hp),
    (characteristic hK hKc).hasCompactSupport.mul_right⟩

omit [MeasurableSpace Y] [BorelSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [TotallyDisconnectedSpace Y] [SecondCountableTopology Y] in
private theorem exists_test_bound (g : SchwartzBruhat Y) : ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C := by
  obtain ⟨C, hC⟩ := g.hasCompactSupport.exists_bound_of_continuousOn g.continuous.continuousOn
  refine ⟨max C 0, fun y => ?_⟩
  by_cases hy : y ∈ tsupport (g : Y → ℂ)
  · exact (hC y hy).trans (le_max_left _ _)
  · simp [image_eq_zero_of_notMem_tsupport hy]

section Local

variable [hausdorffX : T2Space X] [compactX : LocallyCompactSpace X]
  [disconnectedX : TotallyDisconnectedSpace X] [μ.IsOpenPosMeasure] [SigmaFinite ν]

/-- If the pullback of a distribution by test pushforward has a locally integrable
 density near a point, the original distribution has a local density near its image. -/
def PushforwardLocalDensityStatement [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] [BorelSpace X] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y] [SecondCountableTopology Y] [BorelSpace Y] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (ν : Measure Y) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] [SigmaFinite ν] (p : X → Y)
    (P : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y) (D : Distribution Y)
    (U : Set X) (x : X) : Prop :=
  Continuous p → SchwartzBruhat.IsTestPushforward μ ν p P → IsOpen U → x ∈ U →
  (∃ θ : X → ℂ, LocallyIntegrableOn θ U μ ∧ ∀ f : SchwartzBruhat X,
    support (f : X → ℂ) ⊆ U → D (P f) = ∫ z, θ z * f z ∂μ) →
  ∃ V : Set Y, IsOpen V ∧ p x ∈ V ∧ ∃ ρ : Y → ℂ, Integrable ρ ν ∧
    ∀ g : SchwartzBruhat Y, support (g : Y → ℂ) ⊆ V → D g = ∫ y, ρ y * g y ∂ν

/-- A compact clopen source cutoff has a positive pushed density at the image point.
 Divide by its constant value near that point and use Radon–Nikodym on the weighted cutoff. -/
theorem pushforwardLocalDensity (D : Distribution Y) (U : Set X) (x : X) :
    PushforwardLocalDensityStatement μ ν p P D U x := by
  rintro hp hP hU hx ⟨θ, hθ, hD⟩
  obtain ⟨K, hKc, hK, hxK, hKU⟩ := exists_compact_clopen (hU.mem_nhds hx)
  let φ := characteristic hK hKc
  obtain ⟨r, hr, hm⟩ := hP.exists_compactClopenDensity hp hK hKc
  let a := P φ (p x)
  let V : Set Y := {y | P φ y = a}
  have hV : IsOpen V := (P φ).locallyConstant.isOpen_fiber a
  have ha : a ≠ 0 := by
    intro ha
    have hv0 : (μ.restrict K).map p V = 0 := by
      rw [hm, withDensity_apply _ hV.measurableSet]
      apply setLIntegral_eq_zero hV.measurableSet
      intro y hy
      have h := (hr y).symm.trans (hy.trans ha)
      simpa using h
    rw [Measure.map_apply hp.measurable hV.measurableSet,
      Measure.restrict_apply (hp.measurable hV.measurableSet)] at hv0
    exact (hV.preimage hp).inter hK.2 |>.measure_pos μ ⟨x, rfl, hxK⟩ |>.ne' hv0
  have hAC : (μ.restrict K).map p ≪ ν := by
    rw [hm]; exact withDensity_absolutelyContinuous _ _
  obtain ⟨ρ, hρ, hρint⟩ := integrablePushforward (μ := μ.restrict K) (ν := ν) hp.measurable hAC
    θ (hθ.integrableOn_compact_subset hKU hKc)
  refine ⟨V, hV, rfl, fun y => a⁻¹ * ρ y, hρ.const_mul _, fun g hg => ?_⟩
  let f := cutoffPullback hp hK hKc g
  have hf : support (f : X → ℂ) ⊆ U := by
    intro z hz
    apply hKU
    by_contra h
    exact hz (by simp [f, cutoffPullback, characteristic_apply, h])
  have hfg : P f = a • g := by
    apply Hecke.TestFunction.ext
    intro y
    have hprod : P f = ⟨fun y => P φ y * g y, (P φ).locallyConstant.mul g.locallyConstant,
        (P φ).hasCompactSupport.mul_right⟩ := by
      let q : LocallyConstant Y ℂ := ⟨fun y => P φ y * g y,
        (P φ).locallyConstant.mul g.locallyConstant⟩
      suffices hq : Distribution.density ν ⟨P f, (P f).locallyConstant⟩ =
          Distribution.density ν q from
        Hecke.TestFunction.ext fun t => congrArg (fun m : LocallyConstant Y ℂ => m t)
          (Distribution.RenardHaar.density_injective ν hq)
      ext k
      change (∫ y, P f y * k y ∂ν) = ∫ y, (P φ y * g y) * k y ∂ν
      let t : SchwartzBruhat Y := ⟨fun y => g y * k y, g.locallyConstant.mul k.locallyConstant,
        g.hasCompactSupport.mul_right⟩
      rw [hP f k, show (∫ y, (P φ y * g y) * k y ∂ν) = ∫ y, P φ y * t y ∂ν by
        congr 1
        funext y
        exact mul_assoc _ _ _]
      rw [hP φ t]
      congr 1
      funext z
      exact mul_assoc _ _ _
    rw [hprod]
    change P φ y * g y = a * g y
    by_cases hy : g y = 0
    · simp [hy]
    · rw [show P φ y = a from hg hy]
  have hid := hD f hf
  rw [hfg, map_smul, smul_eq_mul] at hid
  have hint : (∫ z, θ z * f z ∂μ) = ∫ z in K, θ z * g (p z) ∂μ := by
    rw [← integral_indicator hK.2.measurableSet]
    congr 1
    funext z
    by_cases hz : z ∈ K <;> simp [f, cutoffPullback, characteristic_apply, hz]
  rw [hint, ← hρint g g.continuous.measurable (exists_test_bound g)] at hid
  simp_rw [mul_assoc, integral_const_mul]
  rw [← hid, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

end Local

end Langlands.HarmonicAnalysis
