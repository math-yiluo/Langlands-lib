import Langlands.HarmonicAnalysis.Distribution.RenardModularStatements
import Langlands.Analysis.Local.ModularCharacterRegularityProof
import Langlands.Analysis.Local.CompactOpenIndexHaarProof
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensityFinite

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Topology

namespace Langlands.HarmonicAnalysis.Distribution.RenardModular

universe uG

section Helpers

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

private theorem nonarchimedean : NonarchimedeanGroup G where
  is_nonarchimedean U hU := by
    obtain ⟨K, _, hK⟩ :=
      ((Langlands.Topology.LocallyProfiniteProof.vanDantzig G).mp
        Langlands.Topology.isLocallyProfinite_of_mathlib).2 U hU
    exact ⟨K, hK⟩

private theorem modular_locallyConstant :
    IsLocallyConstant (Measure.modularCharacter (G := G)) := by
  let := nonarchimedean (G := G)
  exact Langlands.Haar.isLocallyConstant_modularCharacter

variable [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
private theorem integral_unique_complex (ν μ : Measure G) [μ.IsHaarMeasure]
    [IsFiniteMeasureOnCompacts ν] [IsMulLeftInvariant ν]
    {f : G → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∫ x, f x ∂ν) =
      ((haarScalarFactor ν μ : ℝ) : ℂ) * ∫ x, f x ∂μ := by
  have hiν := hf.integrable_of_hasCompactSupport hfc (μ := ν)
  have hiμ := hf.integrable_of_hasCompactSupport hfc (μ := μ)
  have hr := integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν μ
    (Complex.continuous_re.comp hf) (hfc.comp_left (g := Complex.re) rfl)
  have him := integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν μ
    (Complex.continuous_im.comp hf) (hfc.comp_left (g := Complex.im) rfl)
  rw [integral_smul_nnreal_measure] at hr him
  change (∫ x, (f x).re ∂ν) = _ at hr
  change (∫ x, (f x).im ∂ν) = _ at him
  simp only [Function.comp_apply, NNReal.smul_def, smul_eq_mul] at hr him
  have hrν := integral_re hiν
  have hrμ := integral_re hiμ
  have himν := integral_im hiν
  have himμ := integral_im hiμ
  simp only [RCLike.re_eq_complex_re] at hrν hrμ
  simp only [RCLike.im_eq_complex_im] at himν himμ
  rw [hrν, hrμ] at hr
  rw [himν, himμ] at him
  apply Complex.ext
  · simpa only [
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      NNReal.smul_def, smul_eq_mul] using hr
  · simpa only [
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      NNReal.smul_def, smul_eq_mul] using him

omit [T2Space G] [TotallyDisconnectedSpace G] in
private theorem integral_right (μ : Measure G) [μ.IsHaarMeasure]
    (f : SchwartzBruhat G) (g : G) :
    (∫ x, f (x * g) ∂μ) =
      ((Measure.modularCharacter g : ℝ) : ℂ) * ofMeasure μ f := by
  rw [← integral_map (measurable_mul_const g).aemeasurable
    f.continuous.aestronglyMeasurable]
  rw [integral_unique_complex _ μ f.continuous f.hasCompactSupport]
  rw [← modularCharacterFun_eq_haarScalarFactor μ g]
  rfl

omit [T2Space G] [TotallyDisconnectedSpace G] in
private theorem automorphism_factor (μ : Measure G) [μ.IsHaarMeasure]
    (σ : G ≃ₜ* G) :
    haarScalarFactor (μ.map σ) μ = renardAutomorphismModule σ := by
  let η : Measure G := haar
  have heq : haarScalarFactor μ (μ.map σ) = mulEquivHaarChar σ := by
    calc
      _ = haarScalarFactor μ η * haarScalarFactor η (μ.map σ) :=
        haarScalarFactor_eq_mul _ _ _
      _ = haarScalarFactor μ η *
          (haarScalarFactor η (η.map σ) * haarScalarFactor (η.map σ) (μ.map σ)) := by
        rw [haarScalarFactor_eq_mul η (η.map σ) (μ.map σ)]
      _ = mulEquivHaarChar σ *
          (haarScalarFactor μ η * haarScalarFactor η μ) := by
        rw [haarScalarFactor_map]
        change _ = haarScalarFactor η (η.map σ) * _
        ac_rfl
      _ = mulEquivHaarChar σ := by
        rw [← haarScalarFactor_eq_mul, haarScalarFactor_self, mul_one]
  apply mul_left_cancel₀ (mulEquivHaarChar_pos σ).ne'
  rw [← heq, ← haarScalarFactor_eq_mul, haarScalarFactor_self, heq]
  simp [renardAutomorphismModule, (mulEquivHaarChar_pos σ).ne']

private theorem ofMeasure_ne_zero (μ : Measure G) [μ.IsHaarMeasure] :
    ofMeasure μ ≠ 0 := by
  let := nonarchimedean (G := G)
  obtain ⟨K, hK, _⟩ := Langlands.compactOpenSubgroupBasis G Set.univ (by simp)
  let f : SchwartzBruhat G :=
    Langlands.Hecke.TestFunction.characteristic ⟨K.isClosed, K.isOpen⟩ hK
  have hv : ofMeasure μ f = ((μ (K : Set G)).toReal : ℂ) := by
    change (∫ x, f x ∂μ) = _
    change (∫ x, (K : Set G).indicator (fun _ => (1 : ℂ)) x ∂μ) = _
    rw [integral_indicator K.isOpen.measurableSet]
    simp [measureReal_def]
  intro h
  have h0 := LinearMap.congr_fun h f
  rw [hv] at h0
  simp only [LinearMap.zero_apply] at h0
  have hpos : 0 < (μ (K : Set G)).toReal :=
    ENNReal.toReal_pos (K.isOpen.measure_ne_zero μ ⟨1, K.one_mem⟩) hK.measure_ne_top
  exact (ne_of_gt hpos) (by exact_mod_cast h0)


private def modularDensity : LocallyConstant G ℂ :=
  ⟨fun x => ((Measure.modularCharacter x : ℝ) : ℂ),
    modular_locallyConstant.comp (fun x : ℝ≥0 => ((x : ℝ) : ℂ))⟩

private theorem map_density_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (η : Measure X) (e : X ≃ᵐ Y) (w : X → ℝ≥0∞) :
    (η.withDensity w).map e = (η.map e).withDensity (fun y => w (e.symm y)) := by
  have hcomp (v : Y → ℝ≥0∞) :
      (η.withDensity (fun x => v (e x))).map e = (η.map e).withDensity v := by
    ext s hs
    rw [e.measurableEmbedding.map_apply,
      withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
      e.measurableEmbedding.restrict_map, e.measurableEmbedding.lintegral_map]
  convert hcomp (fun y => w (e.symm y)) using 1
  simp only [e.symm_apply_apply]

private theorem integral_inversion_reference (f : SchwartzBruhat G) :
    (∫ x, f x⁻¹ ∂(haar : Measure G)) = density haar (modularDensity (G := G)) f := by
  let η : Measure G := haar
  let w : G → ℝ≥0 := Measure.modularCharacter
  have hw : Continuous w := modular_locallyConstant.continuous
  let ν := η.withDensity (fun x => (w x : ℝ≥0∞))
  let : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_coe hw
  have hprod (x : G) : (w x⁻¹ : ℝ≥0∞) * w x = 1 := by
    simp only [w, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel, map_one, ENNReal.coe_one]
  have hνmap (g : G) : ν.map (· * g) = ν := by
    have : (η.map (· * g)).Regular := Regular.map (Homeomorph.mulRight g)
    have hmap : η.map (· * g) = Measure.modularCharacter g • η := by
      change η.map (· * g) = modularCharacterFun g • η
      rw [modularCharacterFun_eq_haarScalarFactor η g]
      exact isMulLeftInvariant_eq_smul_of_regular _ η
    change (η.withDensity _).map (Homeomorph.mulRight g).toMeasurableEquiv = _
    rw [map_density_equiv]
    change (η.map (· * g)).withDensity (fun x => (w (x * g⁻¹) : ℝ≥0∞)) = _
    rw [hmap]
    change (((Measure.modularCharacter g : ℝ≥0∞) • η).withDensity _) = _
    rw [withDensity_smul_measure]
    rw [← withDensity_smul (Measure.modularCharacter g : ℝ≥0∞) (by fun_prop)]
    congr 1
    funext x
    change (w g : ℝ≥0∞) * w (x * g⁻¹) = w x
    simp only [w, map_mul, ENNReal.coe_mul]
    calc
      _ = (Measure.modularCharacter x : ℝ≥0∞) *
          ((Measure.modularCharacter g⁻¹ : ℝ≥0∞) * Measure.modularCharacter g) := by ring
      _ = _ := by rw [hprod]; simp
  let : IsMulRightInvariant ν := ⟨hνmap⟩
  let := nonarchimedean (G := G)
  obtain ⟨K, hK, _⟩ := Langlands.compactOpenSubgroupBasis G Set.univ (by simp)
  have hmass : ν.inv (K : Set G) = η (K : Set G) := by
    rw [Measure.inv_apply, inv_coe_set]
    change (η.withDensity _) (K : Set G) = _
    rw [withDensity_apply _ K.isOpen.measurableSet]
    calc
      (∫⁻ x in (K : Set G), (w x : ℝ≥0∞) ∂η) = ∫⁻ x in (K : Set G), 1 ∂η := by
        apply setLIntegral_congr_fun K.isOpen.measurableSet
        intro x hx
        have hx1 := Langlands.Haar.modularCharacter_eq_one_of_mem_compact
          K.toSubgroup hK hx
        simp only [w, hx1, ENNReal.coe_one]
      _ = _ := by simp
  have hc : haarScalarFactor ν.inv η = 1 := by
    have heq := measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measurableSet
      ν.inv η K.isOpen.measurableSet hK.closure
    rw [hmass] at heq
    have he : (haarScalarFactor ν.inv η : ℝ≥0∞) = 1 :=
      (ENNReal.mul_eq_right
        (K.isOpen.measure_ne_zero η ⟨1, K.one_mem⟩) hK.measure_ne_top).mp heq.symm
    exact_mod_cast he
  have hi := integral_unique_complex ν.inv η (GroupAction.inversionTests f).continuous
    (GroupAction.inversionTests f).hasCompactSupport
  rw [hc] at hi
  simp only [NNReal.coe_one, Complex.ofReal_one, one_mul] at hi
  rw [Measure.inv, integral_map measurable_inv.aemeasurable
    (GroupAction.inversionTests f).continuous.aestronglyMeasurable] at hi
  simp only [GroupAction.inversionTests_apply, inv_inv] at hi
  rw [integral_withDensity_eq_integral_smul hw.measurable] at hi
  exact hi.symm

private theorem inversion_eq_density (μ : Measure G) [μ.IsHaarMeasure] :
    GroupAction.inversionDistributions (ofMeasure μ) = density μ (modularDensity (G := G)) := by
  ext f
  have hi := integral_unique_complex μ haar (GroupAction.inversionTests f).continuous
    (GroupAction.inversionTests f).hasCompactSupport
  have hd := integral_unique_complex μ haar (multiplyTest modularDensity f).continuous
    (multiplyTest modularDensity f).hasCompactSupport
  change (∫ x, f x⁻¹ ∂μ) = density μ modularDensity f
  calc
    _ = ((haarScalarFactor μ haar : ℝ) : ℂ) * ∫ x, f x⁻¹ ∂haar := hi
    _ = ((haarScalarFactor μ haar : ℝ) : ℂ) * density haar modularDensity f := by
      rw [integral_inversion_reference]
    _ = _ := hd.symm

end Helpers

theorem translation : TranslationStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _
  have hr (g : G) :
      GroupAction.rightDistributions g (ofMeasure μ) =
        ((renardModular g : ℝ) : ℂ) • ofMeasure μ := by
    ext f
    simpa only [GroupAction.rightDistributions_apply, ofMeasure_apply,
      GroupAction.rightTests_apply, LinearMap.smul_apply, smul_eq_mul,
      renardModular_apply] using
      integral_right μ f g⁻¹
  refine ⟨hr, ?_⟩
  intro f h h'
  calc
    (∫ x, f (h' * x * h⁻¹) ∂μ) =
        ∫ x, f (x * h⁻¹) ∂μ :=
      integral_mul_left_eq_self (fun x => f (x * h⁻¹)) h'
    _ = _ := integral_right μ f h⁻¹

theorem regularity : RegularityStatement.{uG} := by
  intro G _ _ _ _ _ _
  let := nonarchimedean (G := G)
  refine ⟨fun g => modularCharacterFun_pos g⁻¹,
    modular_locallyConstant.comp_continuous continuous_inv,
    (modular_locallyConstant.comp_continuous continuous_inv).continuous, ?_⟩
  intro K hK g hg
  exact Langlands.Haar.modularCharacter_eq_one_of_mem_compact K hK (K.inv_mem hg)

theorem automorphism : AutomorphismStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ σ
  have hi (f : SchwartzBruhat G) : (∫ x, f (σ x) ∂μ) =
      ((renardAutomorphismModule σ : ℝ) : ℂ) * ofMeasure μ f := by
    rw [← integral_map (φ := (σ : G → G)) σ.measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
    rw [integral_unique_complex _ μ f.continuous f.hasCompactSupport,
      automorphism_factor μ σ]
    rfl
  refine ⟨?_, hi⟩
  ext f
  exact hi f


theorem inversionDensity : InversionDensityStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _
  refine ⟨modularDensity, ?_, ?_, inversion_eq_density μ⟩
  · intro g
    change ((Measure.modularCharacter g : ℝ) : ℂ) = _
    simp only [renardModular_eq_inv, NNReal.coe_inv, Complex.ofReal_inv, inv_inv]
  · have hleft : IsLeftInvariant (ofMeasure μ) := by
      intro g
      ext f
      simpa only [GroupAction.leftDistributions_apply, ofMeasure_apply,
        GroupAction.leftTests_apply, inv_inv] using
        integral_mul_left_eq_self (fun x => f x) g
    intro g
    rw [← inversion_eq_density μ,
      ← GroupAction.inversionDistributions_leftDistributions, hleft g]

theorem unimodularity : UnimodularityStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _
  have hiff : (∀ g : G, renardModular g = 1) ↔ IsRightInvariant (ofMeasure μ) := by
    constructor
    · intro h g
      simpa [h g] using (translation G μ).1 g
    · intro h g
      have heq := (translation G μ).1 g
      rw [h g] at heq
      have hs : (((renardModular g : ℝ) : ℂ)) = 1 :=
        smul_left_injective ℂ (ofMeasure_ne_zero μ) (by simpa using heq.symm)
      exact_mod_cast hs
  refine ⟨hiff, ?_, ?_, ?_⟩
  · intro hab
    apply hiff.mpr
    intro g
    ext f
    simp only [GroupAction.rightDistributions_apply, ofMeasure_apply,
      GroupAction.rightTests_apply]
    simpa only [hab] using integral_mul_left_eq_self (fun x => f x) g⁻¹
  · intro hcomp g
    exact (regularity G).2.2.2 ⊤ (by simpa using hcomp) g (by simp)
  · intro h g
    obtain ⟨K, hK, hg⟩ := h g
    exact (regularity G).2.2.2 K hK g hg

theorem innerAutomorphism : InnerAutomorphismStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ h σ hσ
  let μ : Measure G := haar
  have heq : (((renardAutomorphismModule σ : ℝ) : ℂ)) • ofMeasure μ =
      (((renardModular h : ℝ) : ℂ)) • ofMeasure μ := by
    ext f
    change (((renardAutomorphismModule σ : ℝ) : ℂ)) * ofMeasure μ f = _
    rw [← (automorphism G μ σ).2 f]
    simpa only [hσ, LinearMap.smul_apply, smul_eq_mul] using
      (translation G μ).2 f h h
  have hs := smul_left_injective ℂ (ofMeasure_ne_zero μ) heq
  exact_mod_cast hs

theorem indexFormula : IndexFormulaStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ σ K hK
  let P := K.toSubgroup.comap σ.toMonoidHom
  let L := K.toSubgroup ⊓ P
  have hPo : IsOpen (P : Set G) := K.isOpen.preimage σ.continuous
  have hPc : IsCompact (P : Set G) := σ.toHomeomorph.isCompact_preimage.mpr hK
  have hLo : IsOpen (L : Set G) := K.isOpen.inter hPo
  have hLc : IsCompact (L : Set G) := hK.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen L hLo) inf_le_left
  have hscale : μ (σ ⁻¹' (K : Set G)) =
      (renardAutomorphismModule σ : ℝ≥0∞) * μ (K : Set G) := by
    have heq := measure_isMulInvariant_eq_smul_of_isCompact_closure_of_measurableSet
      (μ.map σ) μ K.isOpen.measurableSet hK.closure
    rw [Measure.map_apply (f := (σ : G → G)) σ.measurable K.isOpen.measurableSet,
      automorphism_factor μ σ] at heq
    exact heq
  have hmassK : μ (K : Set G) = (L.relIndex K.toSubgroup : ℝ≥0∞) * μ (L : Set G) :=
    (Langlands.Haar.relIndex_mul_measure μ K.toSubgroup L hK K.isOpen hLo inf_le_left).symm
  have hmassP : μ (P : Set G) = (L.relIndex P : ℝ≥0∞) * μ (L : Set G) :=
    (Langlands.Haar.relIndex_mul_measure μ P L hPc hPo hLo inf_le_right).symm
  refine ⟨hscale, hmassK, hmassP, ?_⟩
  have hL0 : μ (L : Set G) ≠ 0 := hLo.measure_ne_zero μ ⟨1, L.one_mem⟩
  have hLtop : μ (L : Set G) ≠ ∞ := hLc.measure_ne_top
  have heq : (renardAutomorphismModule σ : ℝ≥0∞) * (L.relIndex K.toSubgroup : ℝ≥0∞) =
      (L.relIndex P : ℝ≥0∞) := by
    apply (ENNReal.mul_left_inj hL0 hLtop).mp
    rw [mul_assoc, ← hmassK, ← hscale, ← hmassP]
    rfl
  have heq' : renardAutomorphismModule σ * (L.relIndex K.toSubgroup : ℝ≥0) =
      (L.relIndex P : ℝ≥0) := by exact_mod_cast heq
  have : (L.subgroupOf K.toSubgroup).FiniteIndex :=
    Langlands.Haar.finiteIndex_subgroupOf_compact_open K.toSubgroup L hK hLo
  have hn : (L.relIndex K.toSubgroup : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := L.subgroupOf K.toSubgroup))
  exact (eq_div_iff hn).mpr heq'


/-- Renard II.3.7–II.3.8 at the exact published universe and hypotheses. -/
theorem statements : Statements.{uG} :=
  ⟨translation, regularity, inversionDensity, unimodularity, automorphism,
    innerAutomorphism, indexFormula⟩

end Langlands.HarmonicAnalysis.Distribution.RenardModular
