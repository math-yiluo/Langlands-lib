import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicOrbitalMeasure
import Langlands.HarmonicAnalysis.UnitConjugation.CompactConjugationFourier

/-! # Convergence and the constant term formula for parabolic orbital integrals -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer

open MeasureTheory Set QuotientIntegration _root_.Topology
open scoped ENNReal

universe u v

variable (F : Type u) [NontriviallyNormedField F] {A : Type v} [NormedRing A] [NormedAlgebra F A]
  {e : A}

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e

private theorem finiteOnCompacts_orbitalMeasure_of_converges [CompactOpenExhaustion A]
    [MeasurableSpace A] [BorelSpace A] (x : A)
    [MeasurableSpace (LeftQuotient (conjugationCentralizer x))]
    [BorelSpace (LeftQuotient (conjugationCentralizer x))]
    (ν : Measure (LeftQuotient (conjugationCentralizer x))) (hν : OrbitalIntegralConverges x ν) :
    IsFiniteMeasureOnCompacts (ν.map (orbitalPoint x)) := by
  constructor
  intro C hC
  obtain ⟨L, hLc, hLo, hCL⟩ := CompactOpenExhaustion.exists_superset C hC
  let f : SchwartzBruhat A := Hecke.TestFunction.characteristic ⟨hLc.isClosed, hLo⟩ hLc
  have h := hν f
  rw [orbitalIntegrand_eq_comp_orbitalPoint] at h
  have hI : (∫⁻ q, ‖f (orbitalPoint x q)‖ₑ ∂ν) < ∞ :=
    hasFiniteIntegral_iff_enorm.mp h.hasFiniteIntegral
  have hEq : (fun q => ‖f (orbitalPoint x q)‖ₑ) =
      (orbitalPoint x ⁻¹' (L : Set A)).indicator (1 : LeftQuotient (conjugationCentralizer x) → ℝ≥0∞) := by
    funext q
    change ‖(L : Set A).indicator (fun _ => (1 : ℂ)) (orbitalPoint x q)‖ₑ = _
    by_cases hq : orbitalPoint x q ∈ L
    · rw [indicator_of_mem hq, indicator_of_mem (show q ∈ orbitalPoint x ⁻¹' (L : Set A) from hq)]
      simp
    · rw [indicator_of_notMem hq,
        indicator_of_notMem (show q ∉ orbitalPoint x ⁻¹' (L : Set A) from hq), enorm_zero]
  have hΩ : Measurable (orbitalPoint x) := (continuous_orbitalPoint x).measurable
  rw [hEq, lintegral_indicator_one (hΩ hLo.measurableSet)] at hI
  rw [← Measure.map_apply hΩ hLo.measurableSet] at hI
  exact (measure_mono hCL).trans_lt hI

variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  (X : Subalgebra.centralizer F ({e} : Set A)) (K : OpenSubgroup Aˣ)
  [MeasurableSpace (LeftQuotient (conjugationCentralizer X))]
  [BorelSpace (LeftQuotient (conjugationCentralizer X))]
  [MeasurableSpace (LeftQuotient (conjugationCentralizer (X : A)))]
  [BorelSpace (LeftQuotient (conjugationCentralizer (X : A)))]

local notation "Q" => LeftQuotient (conjugationCentralizer X)
local notation "QG" => LeftQuotient (conjugationCentralizer (X : A))

omit [MeasurableSpace (LeftQuotient (conjugationCentralizer (X : A)))]
  [BorelSpace (LeftQuotient (conjugationCentralizer (X : A)))] in
private theorem measurable_parabolicOrbitalPoint [SecondCountableTopology A] :
    Measurable (parabolicOrbitalPoint F X K) := by
  have hk : Measurable fun p : Q × (Upper × K) => p.2.2.val :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hy : Measurable fun p : Q × (Upper × K) => ((orbitalPoint X p.1 : Levi) : A) :=
    measurable_subtype_coe.comp ((continuous_orbitalPoint X).measurable.comp measurable_fst)
  have hz : Measurable fun p : Q × (Upper × K) => (p.2.1 : A) :=
    measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)
  exact ((Units.continuous_coe_inv.measurable.comp hk).mul (hy.add hz)).mul
    (Units.continuous_val.measurable.comp hk)

/-- The parabolic orbital measure formula transfers absolute convergence of the
ambient orbital integrals to all Levi Schwartz–Bruhat tests. -/
theorem orbitalIntegralConverges_levi_of_map_parabolicOrbitalPoint
    [CompactOpenExhaustion A] [SecondCountableTopology A] [ProperSpace Upper]
    (hK : IsCompact (K : Set Aˣ))
    (νG : Measure QG) (νM : Measure Q) (ν : Measure Upper) [ν.IsAddHaarMeasure] [SFinite ν]
    (μK : Measure K) [μK.IsHaarMeasure] (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hmap : (νM.prod (ν.prod μK)).map (parabolicOrbitalPoint F X K) =
      c • νG.map (orbitalPoint (X : A)))
    (hνG : OrbitalIntegralConverges (X : A) νG) :
    OrbitalIntegralConverges X νM := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsFiniteMeasure μK := ⟨isCompact_univ.measure_lt_top⟩
  have : IsFiniteMeasureOnCompacts (νG.map (orbitalPoint (X : A))) :=
    finiteOnCompacts_orbitalMeasure_of_converges (X : A) νG hνG
  let Ω := orbitalPoint X
  let Φ := parabolicOrbitalPoint F X K
  have hΩ : Measurable Ω := (continuous_orbitalPoint X).measurable
  let U : Set Upper := Metric.closedBall 0 1
  have hU : IsCompact U := isCompact_closedBall _ _
  have hUpos : ν U ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds ν (Metric.closedBall_mem_nhds _ zero_lt_one)).ne'
  have hKpos : μK univ ≠ 0 := (isOpen_univ.measure_pos μK Set.univ_nonempty).ne'
  have hfin : IsFiniteMeasureOnCompacts (νM.map Ω) := by
    constructor
    intro C hC
    let f (p : Levi × (Upper × K)) : A :=
      ((p.2.2.val⁻¹ : Aˣ) : A) * ((p.1 : A) + (p.2.1 : A)) * (p.2.2.val : A)
    have hKc : Continuous (fun p : Levi × (Upper × K) => p.2.2.val) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    have hf : Continuous f :=
      ((Units.continuous_coe_inv.comp hKc).mul ((continuous_subtype_val.comp continuous_fst).add
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))).mul
        (Units.continuous_val.comp hKc)
    let D := f '' (C ×ˢ (U ×ˢ univ))
    have hD : IsCompact D := (hC.prod (hU.prod isCompact_univ)).image hf
    have hΦ : Measurable Φ := measurable_parabolicOrbitalPoint F X K
    have hsubset : (Ω ⁻¹' C) ×ˢ (U ×ˢ univ) ⊆ Φ ⁻¹' D := by
      intro p hp
      exact ⟨(Ω p.1, p.2), hp, rfl⟩
    have hle : (νM.prod (ν.prod μK)) ((Ω ⁻¹' C) ×ˢ (U ×ˢ univ)) ≤
        c * (νG.map (orbitalPoint (X : A))) D := by
      calc
        _ ≤ (νM.prod (ν.prod μK)) (Φ ⁻¹' D) := measure_mono hsubset
        _ = _ := by
          rw [← Measure.map_apply hΦ hD.isClosed.measurableSet]
          change (νM.prod (ν.prod μK)).map (parabolicOrbitalPoint F X K) D = _
          rw [hmap, Measure.smul_apply, smul_eq_mul]
    have hlt := hle.trans_lt (ENNReal.mul_lt_top hc.lt_top hD.measure_lt_top)
    rw [Measure.prod_prod, Measure.prod_prod] at hlt
    rw [Measure.map_apply hΩ hC.isClosed.measurableSet]
    by_contra! ht
    rw [top_unique ht, ENNReal.top_mul (mul_ne_zero hUpos hKpos)] at hlt
    exact (lt_irrefl ∞) hlt
  intro f
  rw [orbitalIntegrand_eq_comp_orbitalPoint]
  have hF : Integrable (f : Levi → ℂ) (νM.map Ω) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  exact hF.comp_measurable hΩ

/-- Integration of a Schwartz–Bruhat test against the parabolic orbital measure
is the Levi orbital integral of its compactly averaged constant term. -/
theorem orbitalDistribution_parabolicConstantTerm [IsModuleTopology F A] [ProperSpace Upper]
    [SecondCountableTopology A]
    (he : IsIdempotentElem e) (hK : IsCompact (K : Set Aˣ))
    (νG : Measure QG) (νM : Measure Q) [SFinite νM]
    (ν : Measure Upper) [ν.IsAddHaarMeasure] (μK : Measure K) [IsFiniteMeasure μK] (c : ℝ≥0∞)
    (hc : c ≠ ∞)
    (hmap : (νM.prod (ν.prod μK)).map (parabolicOrbitalPoint F X K) =
      c • νG.map (orbitalPoint (X : A)))
    (hνG : OrbitalIntegralConverges (X : A) νG) (hνM : OrbitalIntegralConverges X νM)
    (f : SchwartzBruhat A) :
    orbitalDistribution X νM hνM
      (parabolicConstantTerm F he ν (compactConjugationAverage (K : Set Aˣ) hK μK f)) =
      c.toReal • orbitalDistribution (X : A) νG hνG f := by
  let Ω := orbitalPoint (X : A)
  let Φ := parabolicOrbitalPoint F X K
  have hΩ : Measurable Ω := (continuous_orbitalPoint (X : A)).measurable
  have hΦ : Measurable Φ := measurable_parabolicOrbitalPoint F X K
  have hF : Integrable (f : A → ℂ) (νG.map Ω) :=
    (integrable_map_measure f.continuous.aestronglyMeasurable hΩ.aemeasurable).mpr (by
      simpa only [orbitalIntegrand_eq_comp_orbitalPoint] using hνG f)
  have hFC : Integrable (f : A → ℂ) ((νM.prod (ν.prod μK)).map Φ) := by
    change Integrable (f : A → ℂ) ((νM.prod (ν.prod μK)).map (parabolicOrbitalPoint F X K))
    rw [hmap]
    exact hF.smul_measure hc
  have hcomp : Integrable (fun p => f (Φ p)) (νM.prod (ν.prod μK)) := hFC.comp_measurable hΦ
  rw [orbitalDistribution_apply, orbitalDistribution_apply, orbitalIntegrand_eq_comp_orbitalPoint,
    orbitalIntegrand_eq_comp_orbitalPoint]
  calc
    _ = ∫ p, f (Φ p) ∂νM.prod (ν.prod μK) := by
      rw [integral_prod _ hcomp]
      apply integral_congr_ae
      filter_upwards [hcomp.prod_right_ae] with q hq
      rw [Function.comp_apply, parabolicConstantTerm_apply, integral_prod _ hq]
      apply integral_congr_ae
      filter_upwards [] with z
      rw [compactConjugationAverage_apply]
      rfl
    _ = ∫ a, f a ∂(νM.prod (ν.prod μK)).map Φ :=
      (integral_map hΦ.aemeasurable f.continuous.aestronglyMeasurable).symm
    _ = _ := by
      change ∫ a, f a ∂(νM.prod (ν.prod μK)).map (parabolicOrbitalPoint F X K) = _
      rw [hmap, integral_smul_measure,
        integral_map hΩ.aemeasurable f.continuous.aestronglyMeasurable]
      rfl

/-- The Levi orbital distribution converges and evaluates the compactly averaged
constant term by the ambient orbital distribution and the factorization scalar. -/
def IdempotentParabolicOrbitalIntegralStatement [IsModuleTopology F A]
    (he : IsIdempotentElem e) (hK : IsCompact (K : Set Aˣ))
    (νG : Measure QG) (νM : Measure Q) (ν : Measure Upper) [IsFiniteMeasureOnCompacts ν]
    (μK : Measure K) [IsFiniteMeasureOnCompacts μK] (c : ℝ≥0∞)
    (hνG : OrbitalIntegralConverges (X : A) νG) : Prop :=
  ∃ hνM : OrbitalIntegralConverges X νM, ∀ f : SchwartzBruhat A,
    orbitalDistribution X νM hνM
      (parabolicConstantTerm F he ν (compactConjugationAverage (K : Set Aˣ) hK μK f)) =
      c.toReal • orbitalDistribution (X : A) νG hνG f

theorem idempotentParabolicOrbitalIntegral [IsModuleTopology F A] [CompactOpenExhaustion A]
    [SecondCountableTopology A] [ProperSpace Upper]
    (he : IsIdempotentElem e) (hK : IsCompact (K : Set Aˣ))
    (νG : Measure QG) (νM : Measure Q) [SFinite νM]
    (ν : Measure Upper) [ν.IsAddHaarMeasure] (μK : Measure K) [μK.IsHaarMeasure]
    (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hmap : (νM.prod (ν.prod μK)).map (parabolicOrbitalPoint F X K) =
      c • νG.map (orbitalPoint (X : A)))
    (hνG : OrbitalIntegralConverges (X : A) νG) :
    IdempotentParabolicOrbitalIntegralStatement F X K he hK νG νM ν μK c hνG := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsFiniteMeasure μK := ⟨isCompact_univ.measure_lt_top⟩
  have hνM := orbitalIntegralConverges_levi_of_map_parabolicOrbitalPoint F X K
    hK νG νM ν μK c hc hmap hνG
  exact ⟨hνM, orbitalDistribution_parabolicConstantTerm F X K he hK
    νG νM ν μK c hc hmap hνG hνM⟩

end Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
