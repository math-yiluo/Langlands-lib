import Langlands.HarmonicAnalysis.CompactSubmersionPushforward
import Langlands.HarmonicAnalysis.Distribution.RenardHaarDensityProof
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Pushforward of Schwartz–Bruhat tests by integration against measures -/

noncomputable section

namespace Langlands.HarmonicAnalysis.SchwartzBruhat

open MeasureTheory Function Set
open Langlands.Hecke.TestFunction
open scoped ENNReal NNReal _root_.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y]

/-- Pushforward of tests relative to the source and target measures, as specified by
 integration against every target test. -/
def IsTestPushforward (μ : Measure X) (ν : Measure Y) (p : X → Y)
    (P : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y) : Prop :=
  ∀ (f : SchwartzBruhat X) (g : SchwartzBruhat Y),
    (∫ y, P f y * g y ∂ν) = ∫ x, f x * g (p x) ∂μ

variable [BorelSpace X] [BorelSpace Y]

private theorem test_integral_ext [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y] (ν : Measure Y) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    {f f' : SchwartzBruhat Y} (h : ∀ g : SchwartzBruhat Y,
      (∫ y, f y * g y ∂ν) = ∫ y, f' y * g y ∂ν) : f = f' := by
  have he : Distribution.density ν ⟨f, f.locallyConstant⟩ =
      Distribution.density ν ⟨f', f'.locallyConstant⟩ := by
    ext g
    exact h g
  exact Hecke.TestFunction.ext fun y => congrArg (fun k : LocallyConstant Y ℂ => k y)
    (Distribution.RenardHaar.density_injective ν he)

private theorem exists_test_of_map_withDensity (μ : Measure X) (ν : Measure Y) {p : X → Y}
    (hp : Measurable p) {K : Set X} (hK : IsClopen K) (hc : IsCompact K)
    (r : LocallyConstant Y ℝ≥0) (hr : HasCompactSupport (r : Y → ℝ≥0))
    (hmap : (μ.restrict K).map p = ν.withDensity (fun y => (r y : ℝ≥0∞))) :
    ∃ f' : SchwartzBruhat Y, ∀ g : SchwartzBruhat Y,
      (∫ y, f' y * g y ∂ν) = ∫ x, characteristic hK hc x * g (p x) ∂μ := by
  let f' : SchwartzBruhat Y := ⟨fun y => ((r y : ℝ) : ℂ),
    r.isLocallyConstant.comp (fun a : ℝ≥0 => ((a : ℝ) : ℂ)),
    hr.comp_left (g := fun a : ℝ≥0 => ((a : ℝ) : ℂ)) (by simp)⟩
  refine ⟨f', fun g => ?_⟩
  calc
    (∫ y, f' y * g y ∂ν) = ∫ y, g y ∂ν.withDensity (fun y => (r y : ℝ≥0∞)) := by
      rw [integral_withDensity_eq_integral_smul r.continuous.measurable]
      rfl
    _ = ∫ x in K, g (p x) ∂μ := by
      rw [← hmap, integral_map hp.aemeasurable g.continuous.measurable.aestronglyMeasurable]
    _ = _ := by
      rw [← integral_indicator hK.isOpen.measurableSet]
      congr 1
      funext x
      by_cases hx : x ∈ K <;> simp [characteristic_apply, hx]

variable [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (ν : Measure Y) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]

omit [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y] [ν.IsOpenPosMeasure] in
private theorem integrable_test_mul (f g : SchwartzBruhat Y) :
    Integrable (fun y => f y * g y) ν :=
  (f.continuous.mul g.continuous).integrable_of_hasCompactSupport
    (f.hasCompactSupport.mul_right)

/-- Compact clopen pushforward densities suffice for a linear pushforward on all tests. -/
theorem exists_testPushforward_of_compactClopen (p : X → Y) (hp : Continuous p)
    (hclopen : ∀ K : Set X, IsCompact K → IsClopen K →
      ∃ r : LocallyConstant Y ℝ≥0, HasCompactSupport (r : Y → ℝ≥0) ∧
        (μ.restrict K).map p = ν.withDensity (fun y => (r y : ℝ≥0∞))) :
    ∃ P : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y, IsTestPushforward μ ν p P := by
  classical
  have hIntegrable (f : SchwartzBruhat X) (g : SchwartzBruhat Y) :
      Integrable (fun x => f x * g (p x)) μ :=
    (f.continuous.mul (g.continuous.comp hp)).integrable_of_hasCompactSupport
      (f.hasCompactSupport.mul_right)
  have hExist (f : SchwartzBruhat X) : ∃ f' : SchwartzBruhat Y,
      ∀ g : SchwartzBruhat Y, (∫ y, f' y * g y ∂ν) = ∫ x, f x * g (p x) ∂μ := by
    let S : Set ℂ := {c | c ∈ Set.range f ∧ c ≠ 0}
    have hS : S.Finite :=
      (finite_range_of_locallyConstant_of_hasCompactSupport f.locallyConstant
        f.hasCompactSupport).subset (fun _ hc => hc.1)
    let : Fintype S := hS.fintype
    let φ (c : S) : SchwartzBruhat X := characteristic
      (f.locallyConstant.isClopen_fiber c.val) (isCompact_fiber f c.property.2)
    have hφ (c : S) : ∃ f' : SchwartzBruhat Y, ∀ g : SchwartzBruhat Y,
        (∫ y, f' y * g y ∂ν) = ∫ x, φ c x * g (p x) ∂μ := by
      obtain ⟨r, hr, hmap⟩ := hclopen {x | f x = c.val} (isCompact_fiber f c.property.2)
        (f.locallyConstant.isClopen_fiber c.val)
      obtain ⟨q, hq⟩ := exists_test_of_map_withDensity μ ν hp.measurable
        (f.locallyConstant.isClopen_fiber c.val) (isCompact_fiber f c.property.2) r hr hmap
      exact ⟨q, hq⟩
    choose φ' hφ' using hφ
    have hf : f = ∑ c : S, c.val • φ c := by
      apply Hecke.TestFunction.ext
      intro x
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, φ, characteristic_apply]
      by_cases hx : f x = 0
      · simp [hx, fun c : S => (Ne.symm c.property.2 : (0 : ℂ) ≠ c.val)]
      · let c : S := ⟨f x, ⟨⟨x, rfl⟩, hx⟩⟩
        rw [Finset.sum_eq_single c]
        · simp [c]
        · intro b _ hbc
          have hxb : f x ≠ b.val := fun h => hbc (Subtype.ext h.symm)
          simp [hxb]
        · simp
    refine ⟨∑ c : S, c.val • φ' c, fun g => ?_⟩
    conv_rhs => rw [hf]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ (fun c _ => (hIntegrable (φ c) g).const_mul c.val),
      integral_finsetSum _ (fun c _ =>
        (integrable_test_mul ν (φ' c) g).const_mul c.val)]
    simp only [integral_const_mul, hφ']
  choose P hP using hExist
  let L : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y :=
    { toFun := P
      map_add' f h := by
        apply test_integral_ext ν
        intro g
        simp only [hP, Submodule.coe_add, Pi.add_apply, add_mul]
        rw [integral_add (hIntegrable f g) (hIntegrable h g),
          integral_add (integrable_test_mul ν (P f) g) (integrable_test_mul ν (P h) g), hP, hP]
      map_smul' a f := by
        apply test_integral_ext ν
        intro g
        simp only [hP, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
          integral_const_mul, RingHom.id_apply] }
  exact ⟨L, hP⟩

omit [IsFiniteMeasureOnCompacts μ] in
/-- Pushforward commutes with pullback by measure-preserving homeomorphisms
 that intertwine the point map. -/
theorem IsTestPushforward.pullback {p : X → Y}
    {P : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Y} (hP : IsTestPushforward μ ν p P)
    (a : X ≃ₜ X) (b : Y ≃ₜ Y) (ha : MeasurePreserving a μ μ) (hb : MeasurePreserving b ν ν)
    (h : ∀ x, p (a x) = b (p x)) (f : SchwartzBruhat X) :
    P (Hecke.TestFunction.pullback a f) = Hecke.TestFunction.pullback b (P f) := by
  apply test_integral_ext ν
  intro g
  rw [hP _ g]
  calc
    (∫ x, Hecke.TestFunction.pullback a f x * g (p x) ∂μ) =
        ∫ x, f x * Hecke.TestFunction.pullback b.symm g (p x) ∂μ := by
      calc
        _ = ∫ x, f (a x) * g (b.symm (p (a x))) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by simp [h]
        _ = _ := ha.integral_comp a.toMeasurableEquiv.measurableEmbedding
          (fun x => f x * g (b.symm (p x)))
    _ = ∫ y, P f y * Hecke.TestFunction.pullback b.symm g y ∂ν := (hP _ _).symm
    _ = ∫ y, Hecke.TestFunction.pullback b (P f) y * g y ∂ν := by
      calc
        _ = ∫ y, P f (b y) * g (b.symm (b y)) ∂ν :=
          (hb.integral_comp b.toMeasurableEquiv.measurableEmbedding
            (fun y => P f y * g (b.symm y))).symm
        _ = _ := by simp

section AdditiveSubmersion

variable {k V W : Type*} [NontriviallyNormedField k] [ProperSpace k]
  [NormedAddCommGroup V] [NormedSpace k V] [FiniteDimensional k V] [IsUltrametricDist V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace k W] [FiniteDimensional k W]
  [LocallyCompactSpace W] [TotallyDisconnectedSpace W] [MeasurableSpace W] [BorelSpace W]

/-- A strictly differentiable submersion on an open subset of an ultrametric vector
space pushes its Schwartz–Bruhat tests to tests for additive Haar measure. -/
theorem exists_testPushforward_of_additiveSubmersion
    (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure W) [ν.IsAddHaarMeasure]
    {U : Set V} (hU : IsOpen U) (p : V → W) (hp : ContinuousOn p U)
    (hd : ∀ x ∈ U, ∃ d : V →L[k] W, HasStrictFDerivAt p d x ∧ Surjective d) :
    ∃ P : SchwartzBruhat U →ₗ[ℂ] SchwartzBruhat W,
      IsTestPushforward (μ.comap Subtype.val) ν (p ∘ Subtype.val) P := by
  classical
  let j : U → V := Subtype.val
  have hEmb : Topology.IsOpenEmbedding j := hU.isOpenEmbedding_subtypeVal
  have hj := hEmb.measurableEmbedding
  let := IsFiniteMeasureOnCompacts.comap' μ hEmb.continuous hj
  have hCont : Continuous (p ∘ j) := continuousOn_iff_continuous_domRestrict.mp hp
  apply exists_testPushforward_of_compactClopen (μ.comap j) ν (p ∘ j) hCont
  intro K hc hK
  let C := j '' K
  have hC : IsClopen C := ⟨(hc.image hEmb.continuous).isClosed, hEmb.isOpenMap K hK.isOpen⟩
  have hCU : C ⊆ U := fun _ ⟨x, _, hx⟩ => hx ▸ x.property
  let p' : V → W := C.piecewise p (fun _ => 0)
  have hp' : Continuous p' := by
    apply continuous_piecewise
    · rw [isClopen_iff_frontier_eq_empty.mp hC]
      simp
    · rw [hC.isClosed.closure_eq]
      exact hp.mono hCU
    · exact continuous_const.continuousOn
  let Φ : k × V → W := p' ∘ Prod.snd
  have hΦ : Continuous Φ := hp'.comp continuous_snd
  let f := LocallyConstant.charFn ℝ≥0 hC
  have hfs : tsupport (f : V → ℝ≥0) = C := by
    have h : support (f : V → ℝ≥0) = C := by
      ext x
      change f x ≠ 0 ↔ x ∈ C
      simpa only [not_not] using not_congr (LocallyConstant.charFn_eq_zero ℝ≥0 x hC)
    rw [tsupport, h, hC.isClosed.closure_eq]
  have hfc : HasCompactSupport (f : V → ℝ≥0) := by
    rw [HasCompactSupport, hfs]
    exact hc.image hEmb.continuous
  have hD (x : V) (hx : x ∈ tsupport (f : V → ℝ≥0)) :
      ∃ D : k × V →L[k] W, HasStrictFDerivAt Φ D (0, x) ∧
        Surjective (D.comp (ContinuousLinearMap.inr k k V)) := by
    have hxc : x ∈ C := hfs ▸ hx
    obtain ⟨d, hD, hs⟩ := hd x (hCU hxc)
    have hD' : HasStrictFDerivAt p' d x := hD.congr_of_eventuallyEq (by
      filter_upwards [hC.isOpen.mem_nhds hxc] with z hz
      exact (piecewise_eq_of_mem C p _ hz).symm)
    let snd := ContinuousLinearMap.snd k k V
    have hsnd : HasStrictFDerivAt (Prod.snd : k × V → V) snd ((0 : k), x) :=
      snd.hasStrictFDerivAt
    refine ⟨d.comp snd, hD'.comp ((0 : k), x) hsnd, ?_⟩
    exact hs
  obtain ⟨N, _, h0, r, hrc, hr⟩ := compactSubmersionPushforward k k V W μ ν Φ 0 f hΦ hfc hD
  refine ⟨r, hrc, ?_⟩
  have hf : μ.withDensity (fun x => (f x : ℝ≥0∞)) = μ.restrict C := by
    have he : (fun x => (f x : ℝ≥0∞)) = C.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext x
      by_cases hx : x ∈ C
      · rw [indicator_of_mem hx, (LocallyConstant.charFn_eq_one _ x hC).mpr hx]
        simp
      · rw [indicator_of_notMem hx, (LocallyConstant.charFn_eq_zero _ x hC).mpr hx]
        simp
    rw [he, withDensity_indicator hC.isOpen.measurableSet]
    exact withDensity_one
  have hmap : Measure.map p' (μ.restrict C) = ν.withDensity (fun y => (r y : ℝ≥0∞)) := by
    have h := hr 0 h0
    rw [hf] at h
    exact h
  rw [← hmap]
  ext B hB
  rw [Measure.map_apply hCont.measurable hB, Measure.map_apply hp'.measurable hB,
    Measure.restrict_apply (hCont.measurable hB), Measure.restrict_apply (hp'.measurable hB),
    Measure.comap_apply j hj.injective (fun _ hs => hj.measurableSet_image.mpr hs) μ
      ((hCont.measurable hB).inter hK.isOpen.measurableSet)]
  congr 1
  ext x
  constructor
  · rintro ⟨s, ⟨hsB, hsK⟩, rfl⟩
    have hsC : j s ∈ C := ⟨s, hsK, rfl⟩
    exact ⟨by simpa only [mem_preimage, Function.comp_apply, p', piecewise_eq_of_mem C p _ hsC] using hsB, hsC⟩
  · rintro ⟨hxB, s, hsK, rfl⟩
    have hsC : j s ∈ C := ⟨s, hsK, rfl⟩
    exact ⟨s, ⟨by simpa only [mem_preimage, Function.comp_apply, p', piecewise_eq_of_mem C p _ hsC] using hxB, hsK⟩, rfl⟩

end AdditiveSubmersion

end Langlands.HarmonicAnalysis.SchwartzBruhat
