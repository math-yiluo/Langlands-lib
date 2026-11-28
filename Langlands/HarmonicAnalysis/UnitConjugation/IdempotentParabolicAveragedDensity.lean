import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicDensity
import Langlands.HarmonicAnalysis.UnitConjugation.CompactConjugationFourier
import Langlands.Analysis.Local.UnitsHaarCoordinates
import Langlands.Group.GL.LeviCentralQuotientMeasure

/-! # Local integrability of the density induced by compactly averaged constant terms -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer

open MeasureTheory Set Function _root_.Topology
open scoped ENNReal

universe u v

variable (F : Type u) [NontriviallyNormedField F] {A : Type v} [NormedRing A] [NormedAlgebra F A]
  [IsModuleTopology F A] {e : A}

local notation "Levi" => Subalgebra.centralizer F (Set.singleton e)
local notation "Upper" => offDiagonalCorner F e

private def averagedConstantTermKernel [FiniteDimensional F A] (he : IsIdempotentElem e)
    (K : OpenSubgroup Aˣ) (hK : IsCompact (K : Set Aˣ)) (f : SchwartzBruhat A) :
    SchwartzBruhat (Levi × (Upper × K)) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let E := parabolicFourierHomeomorph F he
  let one : SchwartzBruhat K :=
    ⟨fun _ => 1, IsLocallyConstant.const 1, HasCompactSupport.of_compactSpace _⟩
  let T (p : Levi × (Upper × K)) : A × K :=
    ((conjugationHomeomorph p.2.2.val).symm (E ((p.1, p.2.1), 0)), p.2.2)
  let S (p : A × K) : Levi × (Upper × K) :=
    let c := E.symm (conjugationHomeomorph p.2.val p.1)
    (c.1.1, c.1.2, p.2)
  have hTc : Continuous T := by
    have hk : Continuous fun p : Levi × (Upper × K) => p.2.2.val :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    have hE : Continuous fun p : Levi × (Upper × K) => E ((p.1, p.2.1), 0) :=
      E.continuous.comp
        ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk continuous_const)
    exact (((Units.continuous_coe_inv.comp hk).mul hE).mul
      (Units.continuous_val.comp hk)).prodMk (continuous_snd.comp continuous_snd)
  have hSc : Continuous S := by
    have hk : Continuous fun p : A × K => p.2.val := continuous_subtype_val.comp continuous_snd
    have hE : Continuous fun p : A × K => E.symm (conjugationHomeomorph p.2.val p.1) :=
      E.symm.continuous.comp (((Units.continuous_val.comp hk).mul continuous_fst).mul
        (Units.continuous_coe_inv.comp hk))
    have hd := continuous_fst.comp hE
    exact (continuous_fst.comp hd).prodMk ((continuous_snd.comp hd).prodMk continuous_snd)
  refine (SchwartzBruhat.tensor f one).compLeftInverse T S hTc hSc (fun p => ?_)
  dsimp only [T, S]
  rw [(conjugationHomeomorph p.2.2.val).apply_symm_apply, E.symm_apply_apply]

private theorem averagedConstantTermKernel_apply [FiniteDimensional F A] (he : IsIdempotentElem e)
    (K : OpenSubgroup Aˣ) (hK : IsCompact (K : Set Aˣ)) (f : SchwartzBruhat A)
    (p : Levi × (Upper × K)) :
    averagedConstantTermKernel F he K hK f p =
      f ((conjugationHomeomorph p.2.2.val).symm ((p.1 : A) + (p.2.1 : A))) := by
  change f ((conjugationHomeomorph p.2.2.val).symm
    (parabolicFourierHomeomorph F he ((p.1, p.2.1), 0))) * 1 = _
  rw [parabolicFourierHomeomorph_apply, Submodule.coe_zero, add_zero, mul_one]

variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  [ProperSpace F] [FiniteDimensional F A]

/-- A locally integrable Levi density, tested against the compactly averaged constant term,
defines a distribution given by a locally integrable ambient density. -/
def IdempotentParabolicAveragedDensityStatement (he : IsIdempotentElem e)
    (K : OpenSubgroup Aˣ) (hK : IsCompact (K : Set Aˣ))
    (μK : Measure K) [IsFiniteMeasureOnCompacts μK]
    (μ : AdditiveHaarMeasure A) (μM : AdditiveHaarMeasure Levi)
    (ν : Measure Upper) [IsFiniteMeasureOnCompacts ν] (θ : Levi → ℂ) : Prop :=
  ∃ r : A → ℂ, LocallyIntegrable r μ.measure ∧ ∀ f : SchwartzBruhat A,
    (∫ x, r x * f x ∂μ.measure) =
      ∫ y, θ y * parabolicConstantTerm F he ν
        (compactConjugationAverage (K : Set Aˣ) hK μK f) y ∂μM.measure

private theorem integral_averagedConstantTermKernel (he : IsIdempotentElem e)
    (K : OpenSubgroup Aˣ) (hK : IsCompact (K : Set Aˣ))
    (μK : Measure K) [IsFiniteMeasure μK] (μM : AdditiveHaarMeasure Levi)
    (ν : Measure Upper) [ν.IsAddHaarMeasure]
    (θ : Levi → ℂ) (hθ : LocallyIntegrable θ μM.measure) (f : SchwartzBruhat A) :
    (∫ y, θ y * parabolicConstantTerm F he ν
      (compactConjugationAverage (K : Set Aˣ) hK μK f) y ∂μM.measure) =
      ∫ p : Levi × (Upper × K), θ p.1 * averagedConstantTermKernel F he K hK f p
        ∂(μM.measure.prod (ν.prod μK)) := by
  have : ProperSpace A := FiniteDimensional.proper F A
  have : ProperSpace Levi := FiniteDimensional.proper F Levi
  have : ProperSpace Upper := FiniteDimensional.proper F Upper
  have : SecondCountableTopology Aᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology Aˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  have : SecondCountableTopology K :=
    (IsEmbedding.subtypeVal (p := fun g : Aˣ => g ∈ K)).secondCountableTopology
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let g := averagedConstantTermKernel F he K hK f
  let ρ := μM.measure.prod (ν.prod μK)
  have hθ' : LocallyIntegrable (fun p : Levi × (Upper × K) => θ p.1) ρ := by
    apply locallyIntegrable_iff.mpr
    intro C hC
    let B : Set Levi := Prod.fst '' C
    let D : Set Upper := (Prod.fst ∘ Prod.snd) '' C
    have hB : IsCompact B := hC.image continuous_fst
    have hD : IsCompact D := hC.image (continuous_fst.comp continuous_snd)
    have : IsFiniteMeasure (ν.restrict D) := isFiniteMeasure_restrict.mpr hD.measure_ne_top
    have hBox : IntegrableOn (fun p : Levi × (Upper × K) => θ p.1) (B ×ˢ (D ×ˢ univ)) ρ := by
      rw [IntegrableOn, ← Measure.prod_restrict, ← Measure.prod_restrict, Measure.restrict_univ]
      exact (hθ.integrableOn_isCompact hB).comp_fst ((ν.restrict D).prod μK)
    exact hBox.mono_set fun p hp => ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp, mem_univ _⟩
  have hF : Integrable (fun p => θ p.1 * g p) ρ :=
    hθ'.integrable_smul_right_of_hasCompactSupport g.continuous g.hasCompactSupport
  rw [integral_prod _ hF]
  apply integral_congr_ae
  filter_upwards [hF.prod_right_ae] with y hy
  rw [parabolicConstantTerm_apply, ← integral_const_mul, integral_prod _ hy]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [compactConjugationAverage_apply, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with k
  rw [averagedConstantTermKernel_apply]

theorem idempotentParabolicAveragedDensity [IsUltrametricDist A] (he : IsIdempotentElem e)
    (K : OpenSubgroup Aˣ) (hK : IsCompact (K : Set Aˣ))
    (hval : IsOpenEmbedding (Units.val : Aˣ → A))
    (μG : Measure Aˣ) [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
    (μ : AdditiveHaarMeasure A) (μM : AdditiveHaarMeasure Levi)
    (ν : Measure Upper) [ν.IsAddHaarMeasure] (θ : Levi → ℂ)
    (hθ : LocallyIntegrable θ μM.measure) :
    let μK := μG.comap (K.toSubgroup.subtype : K →* Aˣ)
    letI : μK.IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance)
      (f := K.toSubgroup.subtype) μG K.isOpen.isOpenEmbedding_subtypeVal
    IdempotentParabolicAveragedDensityStatement F he K hK μK μ μM ν θ := by
  have : ProperSpace A := FiniteDimensional.proper F A
  have : ProperSpace Levi := FiniteDimensional.proper F Levi
  have : ProperSpace Upper := FiniteDimensional.proper F Upper
  have : SecondCountableTopology Aˣ := hval.isEmbedding.secondCountableTopology
  have : SecondCountableTopology K :=
    (IsEmbedding.subtypeVal (p := fun g : Aˣ => g ∈ K)).secondCountableTopology
  dsimp only
  let μK := μG.comap (K.toSubgroup.subtype : K →* Aˣ)
  have : μK.IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance)
    (f := K.toSubgroup.subtype) μG K.isOpen.isOpenEmbedding_subtypeVal
  have : μK.IsMulRightInvariant := Measure.IsMulRightInvariant.comap μG
    (f := K.toSubgroup.subtype) K.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsFiniteMeasure μK := ⟨isCompact_univ.measure_lt_top⟩
  have : μK.IsInvInvariant := Langlands.isInvInvariant_of_isMulRightInvariant μK
  let C := Units.val '' (K : Set Aˣ)
  have hCc : IsCompact C := hK.image Units.continuous_val
  have hCo : IsOpen C := hval.isOpenMap _ K.isOpen
  have hUnits : ∀ a ∈ C, IsUnit a := by
    rintro a ⟨g, _, rfl⟩
    exact g.isUnit
  let j : K → A := fun k => ((k.val⁻¹ : Aˣ) : A)
  let jK : K → Aˣ := Subtype.val
  have hj₀ : Measurable jK := measurable_subtype_coe
  have hj₁ : Measurable (Units.val : Aˣ → A) := Units.continuous_val.measurable
  have hInv : Measurable (Inv.inv : K → K) := by
    change Measurable (Inv.inv : K.toSubgroup → K.toSubgroup)
    exact continuous_inv.measurable
  have hj : Measurable j := (hj₁.comp hj₀).comp hInv
  have hjK : μK.map jK = μG.restrict (K : Set Aˣ) :=
    map_comap_subtype_coe K.isOpen.measurableSet μG
  let b : ℝ≥0∞ := μG (K : Set Aˣ) * (μ.measure C)⁻¹
  have hjmap : μK.map j = b • μ.measure.restrict C := by
    change μK.map ((Units.val ∘ jK) ∘ Inv.inv) = _
    rw [← Measure.map_map (hj₁.comp hj₀) hInv, Measure.map_inv_eq_self,
      ← Measure.map_map hj₁ hj₀, hjK]
    exact Langlands.Analysis.map_val_restrict_compactOpen hval μG μ.measure K.toSubgroup hK K.isOpen
  let V (p : Levi × (Upper × K)) : A × (Levi × Upper) := (j p.2.2, (p.1, p.2.1))
  have hV : Measurable V :=
    (hj.comp (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hR : MeasurePreserving (fun p : Levi × (Upper × K) => (p.2.2, (p.1, p.2.1)))
      (μM.measure.prod (ν.prod μK)) (μK.prod (μM.measure.prod ν)) :=
    Measure.measurePreserving_swap.comp (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc μM.measure ν μK))
  have hVmap : (μM.measure.prod (ν.prod μK)).map V =
      b • (μ.measure.restrict C).prod (μM.measure.prod ν) := by
    change (μM.measure.prod (ν.prod μK)).map
      (Prod.map j id ∘ fun p : Levi × (Upper × K) => (p.2.2, (p.1, p.2.1))) = _
    rw [← Measure.map_map (hj.prodMap measurable_id) hR.measurable, hR.map_eq,
      ← Measure.map_prod_map _ _ hj measurable_id, Measure.map_id, hjmap, Measure.prod_smul_left]
  let hθm := hθ.aestronglyMeasurable
  let θ' := hθm.mk θ
  have hθ'm : Measurable θ' := hθm.measurable_mk
  have hθ' : LocallyIntegrable θ' μM.measure := hθ.congr hθm.ae_eq_mk
  obtain ⟨hΦ, _⟩ := idempotentParabolicAbsoluteContinuity F e he C ⟨hCc.isClosed, hCo⟩
    hUnits μ.measure μM.measure ν μ.measure
  obtain ⟨r, hr, hI⟩ := idempotentParabolicDensity F e he C hCc hCo hUnits
    μ.measure μM.measure ν μ.measure θ' hθ'
  change IdempotentParabolicAveragedDensityStatement F he K hK μK μ μM ν θ
  refine ⟨b.toReal • r, hr.smul _, fun f => ?_⟩
  let W (p : A × (Levi × Upper)) : ℂ :=
    θ' p.2.1 * f (parabolicChartConjugation F e C p)
  have hW : Measurable W := (hθ'm.comp (measurable_fst.comp measurable_snd)).mul
    (f.continuous.measurable.comp hΦ.measurable)
  have hWV (p : Levi × (Upper × K)) :
      θ' p.1 * averagedConstantTermKernel F he K hK f p = W (V p) := by
    rw [averagedConstantTermKernel_apply]
    change θ' p.1 * f ((conjugationHomeomorph p.2.2.val).symm ((p.1 : A) + (p.2.1 : A))) =
      θ' p.1 * f (parabolicChartConjugation F e C (V p))
    have hp : (V p).1 ∈ C := ⟨p.2.2.val⁻¹, K.inv_mem p.2.2.property, rfl⟩
    rw [parabolicChartConjugation_of_mem F e hp]
    simp only [parabolicConjugation, V, j, Ring.inverse_unit, inv_inv]
    rfl
  calc
    _ = b.toReal • ∫ x, r x * f x ∂μ.measure := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with x
      exact smul_mul_assoc b.toReal (r x) (f x)
    _ = b.toReal • ∫ p, W p ∂(μ.measure.restrict C).prod (μM.measure.prod ν) := by
      rw [hI f]
    _ = ∫ p, W p ∂(μM.measure.prod (ν.prod μK)).map V := by
      rw [hVmap, integral_smul_measure]
    _ = ∫ p : Levi × (Upper × K), θ' p.1 * averagedConstantTermKernel F he K hK f p
        ∂(μM.measure.prod (ν.prod μK)) := by
      rw [integral_map hV.aemeasurable hW.aestronglyMeasurable]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun p => (hWV p).symm))
    _ = ∫ y, θ' y * parabolicConstantTerm F he ν
        (compactConjugationAverage (K : Set Aˣ) hK μK f) y ∂μM.measure :=
      (integral_averagedConstantTermKernel F he K hK μK μM ν θ' hθ' f).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hθm.ae_eq_mk.symm] with y hy
      exact congrArg (fun c : ℂ => c * parabolicConstantTerm F he ν
        (compactConjugationAverage (K : Set Aˣ) hK μK f) y) hy

end Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
