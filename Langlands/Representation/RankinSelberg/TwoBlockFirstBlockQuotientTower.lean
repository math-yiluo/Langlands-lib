import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientUnfolding
import Langlands.Analysis.Local.QuotientPositiveLifting
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockFiberKernel
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration
open scoped ENNReal CompactlySupported ProbabilityTheory

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance towerInst1 : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance towerInst2 : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance towerInst3 : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance towerInst4 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance towerInst5 : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance towerInst6 : MeasurableSpace F.Carrier := borel _
local instance towerInst7 : BorelSpace F.Carrier := ⟨rfl⟩
local instance towerInst8 (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance towerInst9 (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance towerInst10 (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance towerInst11 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance towerInst12 (n : ℕ) : MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance towerInst13 (n : ℕ) : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance towerInst14 (n : ℕ) : SecondCountableTopology (upperUnipotent n F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance towerInst15 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F.Carrier) :=
  UpperUnipotent.locallyCompactSpace
local instance towerInst16 (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance towerInst17 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance towerInst18 (n : ℕ) : SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance towerInst19 (n : ℕ) : LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance towerInst20 (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance towerInst21 (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance towerInst22 (n : ℕ) : SecondCountableTopology (LeftUnipotentQuotient n F.Carrier) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
local instance towerInst23 : MeasurableSpace (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier) := borel _
local instance towerInst24 : BorelSpace (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier) := ⟨rfl⟩
local instance towerInst25 : MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := borel _
local instance towerInst26 : BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := ⟨rfl⟩
local instance towerInst27 : MeasurableSpace (mixedSubgroup F h) := borel _
local instance towerInst28 : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance towerInst29 : MeasurableSpace (MixedQuotient F h) := borel _
local instance towerInst30 : BorelSpace (MixedQuotient F h) := ⟨rfl⟩

/-- Integrating the block average over the small zero slice gives the exact mixed average. -/
theorem lintegral_fiberPoint_quotientAverageReal
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ)) (hf0 : ∀ x, 0 ≤ f x)
    (g : GeneralLinear (t + 1) F.Carrier) :
    ∫⁻ q, ENNReal.ofReal (quotientAverageReal
        (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier)
        (TwoBlockUnipotentQuotient.blockHaar F.Carrier h) f (fiberPoint h F.Carrier q g))
      ∂νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) 0) =
      ENNReal.ofReal (quotientAverageReal (mixedSubgroup F h) (mixedHaar F h) f
        (Quotient.mk _ g)) := by
  let D : GeneralLinear (m 0 + 1) F.Carrier × upperUnipotent (m 1 + 1) F.Carrier →
      GeneralLinear (t + 1) F.Carrier :=
    fun x => (succBlockShape m h).leviEmbedding F.Carrier (blockPair F.Carrier (x.1, x.2.val))
  have hDc : Continuous D :=
    ((succBlockShape m h).leviEmbeddingContinuous F.Carrier).continuous.comp
      ((continuous_blockPair F.Carrier).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  let Φ : GeneralLinear (m 0 + 1) F.Carrier → ℝ≥0∞ :=
    fun u => ∫⁻ b : upperUnipotent (m 1 + 1) F.Carrier,
      ENNReal.ofReal (f (D (u, b) * g)) ∂unipotentHaar F.Carrier (m 1)
  have hΦ : Measurable Φ :=
    (ENNReal.continuous_ofReal.comp (f.continuous.comp (hDc.mul_const g))).measurable.lintegral_prod_right'
  have hblock (a : upperUnipotent (m 0 + 1) F.Carrier)
      (b : upperUnipotent (m 1 + 1) F.Carrier) (u : GeneralLinear (m 0 + 1) F.Carrier) :
      (TwoBlockUnipotentQuotient.blockUnipotentEquiv h F.Carrier
        ((MeasurableEquiv.piFinTwo _).symm (a, b))).val * firstBlockEmbedding h F.Carrier u =
          D (a.val * u, b) := by
    rw [TwoBlockUnipotentQuotient.blockUnipotentEquiv_apply_val,
      TwoBlockUnipotentQuotient.blockEmbedding_apply, firstBlockEmbedding_apply, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [MeasurableEquiv.piFinTwo, piFinTwoEquiv]
  have hrep (u : GeneralLinear (m 0 + 1) F.Carrier) :
      ENNReal.ofReal (quotientAverageReal
        (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier)
        (TwoBlockUnipotentQuotient.blockHaar F.Carrier h) f
        (fiberPoint h F.Carrier (Quotient.mk _ u) g)) =
      ∫⁻ a : upperUnipotent (m 0 + 1) F.Carrier,
        Φ (a.val * u) ∂unipotentHaar F.Carrier (m 0) := by
    rw [fiberPoint_mk, quotientAverageReal_mk,
      ofReal_integral_eq_lintegral_ofReal
        (integrable_subgroup_mul _ (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F.Carrier)
          (TwoBlockUnipotentQuotient.blockHaar F.Carrier h) f _)
        (Filter.Eventually.of_forall fun _ => hf0 _)]
    have hfm : Measurable (fun b : TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier =>
        ENNReal.ofReal (f (b.val * (firstBlockEmbedding h F.Carrier u * g)))) :=
      (ENNReal.continuous_ofReal.comp
        (f.continuous.comp (continuous_subtype_val.mul_const _))).measurable
    rw [lintegral_blockHaar F h _ hfm]
    apply lintegral_congr
    intro a
    apply lintegral_congr
    intro b
    rw [← mul_assoc, hblock]
  let κA := orbitKernel (upperUnipotent (m 0 + 1) F.Carrier)
    (UpperUnipotent.isClosed (R := F.Carrier)) (unipotentHaar F.Carrier (m 0))
  have hmix : Measurable (mixedSubgroupEquiv F h) :=
    (mixedSubgroupHomeomorph F h).continuous.measurable
  have hmfm : Measurable (fun l : mixedSubgroup F h => ENNReal.ofReal (f (l.val * g))) :=
    (ENNReal.continuous_ofReal.comp
      (f.continuous.comp (continuous_subtype_val.mul_const g))).measurable
  have hmixrep : ENNReal.ofReal (quotientAverageReal (mixedSubgroup F h) (mixedHaar F h) f
      (Quotient.mk _ g)) = ∫⁻ u : normOneSubgroup F (m 0 + 1), Φ u.val ∂normOneHaar F (m 0) := by
    rw [quotientAverageReal_mk, ofReal_integral_eq_lintegral_ofReal
      (integrable_subgroup_mul _ (isClosed_mixedSubgroup F h) (mixedHaar F h) f g)
      (Filter.Eventually.of_forall fun _ => hf0 _), mixedHaar, lintegral_map hmfm hmix]
    have hprod : Measurable (fun x : normOneSubgroup F (m 0 + 1) ×
        upperUnipotent (m 1 + 1) F.Carrier =>
        ENNReal.ofReal (f ((mixedSubgroupEquiv F h x).val * g))) := hmfm.comp hmix
    rw [lintegral_prod _ hprod.aemeasurable]
    rfl
  calc
    _ = ∫⁻ q, ∫⁻ v, Φ v ∂κA q ∂νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) 0) := by
      apply lintegral_congr
      intro q
      induction q using Quotient.inductionOn with
      | h u =>
        rw [hrep, show κA (Quotient.mk _ u) = _ from orbitKernel_mk _ _ _ u,
          lintegral_map hΦ (continuous_subtype_val.mul_const u).measurable]
    _ = ∫⁻ v, Φ v ∂(κA ∘ₘ νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) 0)) :=
      (Measure.lintegral_bind κA.measurable.aemeasurable hΦ.aemeasurable).symm
    _ = ∫⁻ v, Φ v ∂Measure.map Subtype.val (normOneHaar F (m 0)) := by
      rw [show κA ∘ₘ νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) 0) = _ from
        small_orbitKernel_comp_zero F (m 0) νA hνA]
    _ = _ := by rw [lintegral_map hΦ continuous_subtype_val.measurable, hmixrep]

local instance towerBlockQuotientT2 :
    T2Space (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) :=
  leftQuotient_t2Space _ (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F.Carrier)
local instance towerBlockQuotientLocallyCompact :
    LocallyCompactSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) :=
  leftQuotient_locallyCompactSpace _
local instance towerBlockQuotientSecondCountable :
    SecondCountableTopology (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)

/-- The composite zero-slice fiber measure integrates block averages to mixed averages. -/
theorem lintegral_comp_quotientAverageReal
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (νL : Measure (MixedQuotient F h))
    (f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ)) (hf0 : ∀ x, 0 ≤ f x) :
    ∫⁻ z, ENNReal.ofReal (quotientAverageReal
        (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier)
        (TwoBlockUnipotentQuotient.blockHaar F.Carrier h) f z)
      ∂(fiberKernel F h νA hInv 0 ∘ₘ νL) =
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal (mixedSubgroup F h) (mixedHaar F h) f q) ∂νL := by
  have hHm : Measurable (fun z => ENNReal.ofReal (quotientAverageReal
      (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier)
      (TwoBlockUnipotentQuotient.blockHaar F.Carrier h) f z)) :=
    (ENNReal.continuous_ofReal.comp (continuous_quotientAverageReal _
      (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F.Carrier) _ f)).measurable
  rw [Measure.lintegral_bind (fiberKernel F h νA hInv 0).measurable.aemeasurable hHm.aemeasurable]
  apply lintegral_congr
  intro q
  induction q using Quotient.inductionOn with
  | h g =>
    have hfm : Measurable (fun a => fiberPoint h F.Carrier a g) :=
      ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    rw [fiberKernel_mk, lintegral_map hHm hfm]
    exact lintegral_fiberPoint_quotientAverageReal F h νA hνA f hf0 g

/-- The normalized full tower has coefficient exactly one. -/
theorem fiberKernel_zero_comp
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (νL : Measure (MixedQuotient F h))
    (hνL : IsCompatible (mixedSubgroup F h) (generalLinearHaar F.Carrier t) (mixedHaar F h) νL)
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier))
    (hνH : IsCompatible (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (TwoBlockUnipotentQuotient.blockHaar F.Carrier h) νH) :
    fiberKernel F h νA hInv 0 ∘ₘ νL = νH := by
  let H := TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier
  let μH := TwoBlockUnipotentQuotient.blockHaar F.Carrier h
  let μG := generalLinearHaar F.Carrier t
  let κ := fiberKernel F h νA hInv 0
  have hH := TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F.Carrier
  have hL : ∀ f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ), (∀ y, 0 ≤ f y) →
      ∫⁻ z, ENNReal.ofReal (quotientAverageReal H μH f z) ∂(κ ∘ₘ νL) =
        ∫⁻ y, ENNReal.ofReal (f y) ∂μG := by
    intro f hf0
    rw [lintegral_comp_quotientAverageReal F h νA hInv hνA νL f hf0,
      RecursiveIntegration.lintegral_quotientAverageReal _ _ _ _ hνL
        f f.continuous f.hasCompactSupport hf0]
  have hR : ∀ f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ), (∀ y, 0 ≤ f y) →
      ∫⁻ z, ENNReal.ofReal (quotientAverageReal H μH f z) ∂νH =
        ∫⁻ y, ENNReal.ofReal (f y) ∂μG := by
    intro f hf0
    exact RecursiveIntegration.lintegral_quotientAverageReal H μG μH νH hνH
      f f.continuous f.hasCompactSupport hf0
  have hlift : ∀ φ : C_c(TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier, ℝ),
      (∀ q, 0 ≤ φ q) → ∃ f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ),
        (∀ y, 0 ≤ f y) ∧ ∀ q, quotientAverageReal H μH f q = φ q := by
    intro φ hφ
    obtain ⟨f, hf, hf0⟩ := realQuotientPositiveLifting H hH μH φ
    refine ⟨f, hf0 hφ, fun q => ?_⟩
    induction q using Quotient.inductionOn with
    | h g => exact hf g
  have hfin : IsFiniteMeasureOnCompacts (κ ∘ₘ νL) := by
    refine ⟨fun C hC => ?_⟩
    obtain ⟨u, hu1, -, hucs, hu01⟩ :=
      exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
    let φ : C_c(TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier, ℝ) := ⟨u, hucs⟩
    obtain ⟨f, hf0, hfavg⟩ := hlift φ fun q => (hu01 q).1
    calc (κ ∘ₘ νL) C = ∫⁻ q, C.indicator 1 q ∂(κ ∘ₘ νL) :=
        (lintegral_indicator_one hC.isClosed.measurableSet).symm
      _ ≤ ∫⁻ q, ENNReal.ofReal (quotientAverageReal H μH f q) ∂(κ ∘ₘ νL) := by
        apply lintegral_mono
        intro q
        dsimp only
        rw [hfavg q]
        by_cases hq : q ∈ C
        · rw [Set.indicator_of_mem hq]
          change (1 : ENNReal) ≤ ENNReal.ofReal (u q)
          rw [hu1 hq, Pi.one_apply, ENNReal.ofReal_one]
        · rw [Set.indicator_of_notMem hq]
          exact zero_le
      _ = ∫⁻ y, ENNReal.ofReal (f y) ∂μG := hL f hf0
      _ < ⊤ := (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).lintegral_lt_top
  have : (κ ∘ₘ νL).Regular := inferInstance
  have : νH.Regular := hνH.regular
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro φ
  let φr : C_c(TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier, ℝ) :=
    ⟨⟨fun q => (φ q : ℝ), NNReal.continuous_coe.comp φ.continuous⟩,
      φ.hasCompactSupport.comp_left NNReal.coe_zero⟩
  obtain ⟨f, hf0, hfavg⟩ := hlift φr fun q => (φ q).coe_nonneg
  have key : ∀ μ' : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier),
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal H μH f q) ∂μ' =
        ∫⁻ y, ENNReal.ofReal (f y) ∂μG →
      ∫ q, (φ q : ℝ) ∂μ' = (∫⁻ y, ENNReal.ofReal (f y) ∂μG).toReal := by
    intro μ' h'
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => (φ q).coe_nonneg)
      (NNReal.continuous_coe.comp φ.continuous).aestronglyMeasurable, ← h']
    congr 1
    apply lintegral_congr
    intro q
    rw [hfavg q]
    rfl
  rw [key _ (hL f hf0), key _ (hR f hf0)]

/-- The zero small slice preserves the determinant slice of the mixed base. -/
theorem fiberKernel_zero_comp_restrict
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (νL : Measure (MixedQuotient F h))
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier))
    (hcomp : fiberKernel F h νA hInv 0 ∘ₘ νL = νH) (k : ℤ) :
    fiberKernel F h νA hInv 0 ∘ₘ νL.restrict (determinantSlice F h k) =
      νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h k) := by
  let κ := fiberKernel F h νA hInv 0
  let sA := RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) 0
  let sL := determinantSlice F h k
  let sH := TwoBlockUnipotentQuotient.determinantSlice F h k
  have hsL : MeasurableSet sL := measurableSet_determinantSlice F h k
  have hsH : MeasurableSet sH := TwoBlockUnipotentQuotient.measurableSet_determinantSlice F h k
  have hpt : ∀ A, MeasurableSet A → ∀ q,
      κ q (A ∩ sH) = sL.indicator (fun q => κ q A) q := by
    intro A hA q
    induction q using Quotient.inductionOn with
    | h g =>
      have hfm : Measurable (fun a => fiberPoint h F.Carrier a g) :=
        ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
      have hsupport : ∀ a, a ∈ sA →
          (fiberPoint h F.Carrier a g ∈ sH ↔ (Quotient.mk _ g : MixedQuotient F h) ∈ sL) := by
        intro a ha
        change RankinSelberg.determinantOrder F.canonicalTopologicalData (m 0) a = 0 at ha
        rw [show (fiberPoint h F.Carrier a g ∈ sH) ↔ _ from
          fiberPoint_mem_determinantSlice_iff F h a g k, ha, zero_add]
        rfl
      rw [show κ (Quotient.mk _ g) = _ from fiberKernel_mk F h νA hInv 0 g,
        Measure.map_apply hfm (hA.inter hsH), Measure.restrict_apply (hfm (hA.inter hsH))]
      by_cases hg : (Quotient.mk _ g : MixedQuotient F h) ∈ sL
      · rw [Set.indicator_of_mem hg,
          show κ (Quotient.mk _ g) = _ from fiberKernel_mk F h νA hInv 0 g,
          Measure.map_apply hfm hA, Measure.restrict_apply (hfm hA)]
        congr 1
        ext a
        change ((fiberPoint h F.Carrier a g ∈ A ∧ fiberPoint h F.Carrier a g ∈ sH) ∧ a ∈ sA) ↔
          (fiberPoint h F.Carrier a g ∈ A ∧ a ∈ sA)
        exact ⟨fun ha => ⟨ha.1.1, ha.2⟩, fun ha => ⟨⟨ha.1, (hsupport a ha.2).2 hg⟩, ha.2⟩⟩
      · rw [Set.indicator_of_notMem hg]
        have he : ((fun a => fiberPoint h F.Carrier a g) ⁻¹' (A ∩ sH)) ∩ sA = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro a ha
          exact hg ((hsupport a ha.2).1 ha.1.2)
        rw [show RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) 0 = sA from rfl,
          he, measure_empty]
  ext A hA
  change (κ ∘ₘ νL.restrict sL) A = νH.restrict sH A
  rw [Measure.bind_apply hA κ.measurable.aemeasurable, Measure.restrict_apply hA,
    ← lintegral_indicator hsL]
  rw [show (∫⁻ q, sL.indicator (fun q => κ q A) q ∂νL) =
      ∫⁻ q, κ q (A ∩ sH) ∂νL from lintegral_congr fun q => (hpt A hA q).symm]
  rw [← Measure.bind_apply (hA.inter hsH) κ.measurable.aemeasurable, hcomp]

/-- Exact full and same-slice composition for the zero small-slice kernel. -/
abbrev NormalizedTowerStatement
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (νL : Measure (MixedQuotient F h))
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier)) : Prop :=
  (fiberKernel F h νA hInv 0 ∘ₘ νL = νH) ∧
    ∀ k : ℤ, fiberKernel F h νA hInv 0 ∘ₘ νL.restrict (determinantSlice F h k) =
      νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h k)

/-- Compatible measures satisfy the normalized full tower and all its same-slice restrictions. -/
theorem normalized_tower
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
    (hInv : NormOneRightInvariant F (m 0) νA)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (νL : Measure (MixedQuotient F h))
    (hνL : IsCompatible (mixedSubgroup F h) (generalLinearHaar F.Carrier t) (mixedHaar F h) νL)
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier))
    (hνH : IsCompatible (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (TwoBlockUnipotentQuotient.blockHaar F.Carrier h) νH) :
    NormalizedTowerStatement F h νA hInv νL νH := by
  have hc := fiberKernel_zero_comp F h νA hInv hνA νL hνL νH hνH
  exact ⟨hc, fiberKernel_zero_comp_restrict F h νA hInv νL νH hc⟩

end Langlands.RankinSelberg.TwoBlockFirstBlockQuotient
