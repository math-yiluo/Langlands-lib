import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockNormalization
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberProper
import Langlands.Representation.RankinSelberg.RecursiveQuotientIntegrationProof
import Langlands.Analysis.Local.QuotientPositiveLifting
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# The radical tower for the actual lower mixed quotient

The supplied rectangular Haar is unchanged. Its integral-cube mass is the
coefficient of the quotient measure composition in JPSS Section 4.9 (2).
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
open scoped ENNReal CompactlySupported ProbabilityTheory

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerRadicalTowerInstance01 : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance lowerRadicalTowerInstance02 : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance lowerRadicalTowerInstance03 : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance lowerRadicalTowerInstance04 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance lowerRadicalTowerInstance05 : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance lowerRadicalTowerInstance06 : MeasurableSpace F.Carrier := borel _
local instance lowerRadicalTowerInstance07 : BorelSpace F.Carrier := ⟨rfl⟩
local instance lowerRadicalTowerInstance08 (a b : ℕ) : LocallyCompactSpace (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F.Carrier))
local instance lowerRadicalTowerInstance09 (a b : ℕ) : SecondCountableTopology (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F.Carrier))
local instance lowerRadicalTowerInstance10 (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n
local instance lowerRadicalTowerInstance11 (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance lowerRadicalTowerInstance12 (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance lowerRadicalTowerInstance13 (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance lowerRadicalTowerInstance14 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance lowerRadicalTowerInstance15 (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance lowerRadicalTowerInstance16 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance lowerRadicalTowerInstance17 (n : ℕ) : SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerRadicalTowerInstance18 (n : ℕ) : LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance lowerRadicalTowerInstance19 (n : ℕ) : MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance lowerRadicalTowerInstance20 (n : ℕ) : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance lowerRadicalTowerInstance21 (n : ℕ) : SecondCountableTopology (upperUnipotent n F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerRadicalTowerInstance22 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F.Carrier) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerRadicalTowerInstance23 : MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance lowerRadicalTowerInstance24 : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance lowerRadicalTowerInstance25 : SecondCountableTopology (lowerMixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerRadicalTowerInstance26 : LocallyCompactSpace (lowerMixedSubgroup F h) :=
  (isClosed_lowerMixedSubgroup F h).locallyCompactSpace

local notation "R" => Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier
local notation "D" => normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier
local notation "μD" => Measure.prod (normOneHaar F (m 0)) (unipotentHaar F.Carrier (m 1))


local instance lowerRadicalTowerInstance27 : MeasurableSpace (mixedSubgroup F h) := borel _
local instance lowerRadicalTowerInstance28 : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance lowerRadicalTowerInstance29 : SecondCountableTopology (mixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerRadicalTowerInstance30 : LocallyCompactSpace (mixedSubgroup F h) :=
  (isClosed_mixedSubgroup F h).locallyCompactSpace
local instance lowerRadicalTowerInstance31 : MeasurableSpace (MixedQuotient F h) := borel _
local instance lowerRadicalTowerInstance32 : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance lowerRadicalTowerInstance33 : T2Space (MixedQuotient F h) :=
  leftQuotient_t2Space _ (isClosed_mixedSubgroup F h)
local instance lowerRadicalTowerInstance34 : LocallyCompactSpace (MixedQuotient F h) := leftQuotient_locallyCompactSpace _
local instance lowerRadicalTowerInstance35 : SecondCountableTopology (MixedQuotient F h) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
local instance lowerRadicalTowerInstance36 : MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance lowerRadicalTowerInstance37 : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

local notation "O" => Valuation.integer (ValuativeRel.valuation F.Carrier)

/-- Right radical coordinates give the same product Haar as the published left coordinates. -/
theorem lintegral_mixedHaar_radical
    (μR : Measure R) [μR.IsAddHaarMeasure]
    (ψ : GeneralLinear (t + 1) F.Carrier → ℝ≥0∞) (hψ : Measurable ψ) :
    (∫⁻ Z, ∫⁻ a : mixedSubgroup F h,
      ψ (a.val * lowerRadical h F.Carrier Z) ∂mixedHaar F h ∂μR) =
      μR {Z | ∀ i j, Z i j ∈ O} *
        ∫⁻ a : lowerMixedSubgroup F h, ψ a.val ∂lowerMixedHaar F h := by
  have hm : Measurable (mixedSubgroupEquiv F h) :=
    (mixedSubgroupHomeomorph F h).continuous.measurable
  have hDm : Measurable (mixedEmbedding F h : D → GeneralLinear (t + 1) F.Carrier) :=
    continuous_subtype_val.measurable.comp hm
  have hRc : Continuous (lowerRadical h F.Carrier : R → GeneralLinear (t + 1) F.Carrier) :=
    continuous_lowerRadical h F.Carrier
  have hleft : Measurable (fun x : R × D =>
      ψ (mixedEmbedding F h x.2 * lowerRadical h F.Carrier x.1)) :=
    hψ.comp ((hDm.comp measurable_snd).mul (hRc.measurable.comp measurable_fst))
  have hright : Measurable (fun x : R × D =>
      ψ (lowerRadical h F.Carrier x.1 * mixedEmbedding F h x.2)) :=
    hψ.comp ((hRc.measurable.comp measurable_fst).mul (hDm.comp measurable_snd))
  calc
    _ = ∫⁻ Z, ∫⁻ d : D, ψ (mixedEmbedding F h d * lowerRadical h F.Carrier Z)
        ∂μD ∂μR := by
      apply lintegral_congr
      intro Z
      rw [mixedHaar, lintegral_map
        (f := fun a : mixedSubgroup F h => ψ (a.val * lowerRadical h F.Carrier Z))
        (hψ.comp (continuous_subtype_val.mul_const _).measurable) hm]
      rfl
    _ = ∫⁻ d : D, ∫⁻ Z, ψ (mixedEmbedding F h d * lowerRadical h F.Carrier Z)
        ∂μR ∂μD := lintegral_lintegral_swap hleft.aemeasurable
    _ = ∫⁻ d : D, ∫⁻ Z, ψ (lowerRadical h F.Carrier Z * mixedEmbedding F h d)
        ∂μR ∂μD := by
      apply lintegral_congr
      intro d
      have hp : MeasurePreserving
          (fun Z : R => d.2.val.val * Z * (d.1.val⁻¹).val) μR μR := by
        have hp := measurePreserving_radicalChange F μR 0 d.1⁻¹ d.2⁻¹
        change MeasurePreserving (fun Z : R =>
          ((d.2⁻¹).val⁻¹).val * (Z + 0) * (d.1⁻¹).val.val) μR μR at hp
        simpa only [Subgroup.coe_inv, inv_inv, add_zero] using hp
      calc
        _ = ∫⁻ Z, ψ (lowerRadical h F.Carrier
            (d.2.val.val * Z * (d.1.val⁻¹).val) * mixedEmbedding F h d) ∂μR := by
          apply lintegral_congr
          intro Z
          rw [mixedEmbedding_apply, leviEmbedding_blockPair_mul_lowerRadical]
        _ = _ := hp.lintegral_comp
          (hψ.comp (hRc.mul_const (mixedEmbedding F h d)).measurable)
    _ = ∫⁻ Z, ∫⁻ d : D, ψ (lowerRadical h F.Carrier Z * mixedEmbedding F h d)
        ∂μD ∂μR := (lintegral_lintegral_swap hright.aemeasurable).symm
    _ = ∫⁻ a : lowerMixedSubgroup F h, ψ a.val ∂lowerMixedProductMeasure F h μR := by
      rw [lowerMixedProductMeasure,
        lintegral_map (f := fun a : lowerMixedSubgroup F h => ψ a.val)
          (hψ.comp continuous_subtype_val.measurable)
          (lowerMixedSubgroupHomeomorph F h).continuous.measurable,
        lintegral_prod (fun x : R × D => ψ ((lowerMixedSubgroupHomeomorph F h x).val))
          (hψ.comp (continuous_subtype_val.measurable.comp
          (lowerMixedSubgroupHomeomorph F h).continuous.measurable)).aemeasurable]
      rfl
    _ = _ := by rw [lowerMixedProductMeasure_eq_smul, lintegral_smul_measure, smul_eq_mul]

/-- The lower radical integrates the mixed orbital average to the cube multiple
of the normalized lower mixed average, at every representative. -/
theorem lintegral_radicalFiberPoint_quotientAverageReal
    (μR : Measure R) [μR.IsAddHaarMeasure]
    (f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ)) (hf0 : ∀ x, 0 ≤ f x)
    (g : GeneralLinear (t + 1) F.Carrier) :
    (∫⁻ Z, ENNReal.ofReal (quotientAverageReal (mixedSubgroup F h) (mixedHaar F h) f
      (radicalFiberPoint F h Z g)) ∂μR) =
      μR {Z | ∀ i j, Z i j ∈ O} *
        ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h) (lowerMixedHaar F h) f
          (Quotient.mk _ g)) := by
  calc
    _ = ∫⁻ Z, ∫⁻ a : mixedSubgroup F h,
        ENNReal.ofReal (f (a.val * lowerRadical h F.Carrier Z * g)) ∂mixedHaar F h ∂μR := by
      apply lintegral_congr
      intro Z
      rw [radicalFiberPoint_def, quotientAverageReal_mk,
        ofReal_integral_eq_lintegral_ofReal
          (integrable_subgroup_mul _ (isClosed_mixedSubgroup F h) (mixedHaar F h) f _)
          (Filter.Eventually.of_forall fun a => hf0 _)]
      simp only [mul_assoc]
    _ = μR {Z | ∀ i j, Z i j ∈ O} *
        ∫⁻ a : lowerMixedSubgroup F h, ENNReal.ofReal (f (a.val * g)) ∂lowerMixedHaar F h :=
      lintegral_mixedHaar_radical F h μR _
        (ENNReal.continuous_ofReal.comp (f.continuous.comp (continuous_id.mul_const g))).measurable
    _ = _ := by
      rw [quotientAverageReal_mk, ofReal_integral_eq_lintegral_ofReal
        (integrable_subgroup_mul _ (isClosed_lowerMixedSubgroup F h) (lowerMixedHaar F h) f _)
        (Filter.Eventually.of_forall fun a => hf0 _)]


/-- The composite radical kernel integrates mixed averages to cube multiples of
lower mixed averages for every outer measure. -/
theorem lintegral_radicalKernel_comp_quotientAverageReal
    (μR : Measure R) [μR.IsAddHaarMeasure]
    (νL : Measure (LowerMixedQuotient F h))
    (f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ)) (hf0 : ∀ x, 0 ≤ f x) :
    (∫⁻ z, ENNReal.ofReal (quotientAverageReal (mixedSubgroup F h) (mixedHaar F h) f z)
      ∂(radicalKernel F h μR ∘ₘ νL)) =
      μR {Z | ∀ i j, Z i j ∈ O} *
        ∫⁻ q, ENNReal.ofReal (quotientAverageReal (lowerMixedSubgroup F h)
          (lowerMixedHaar F h) f q) ∂νL := by
  have hMm : Measurable (fun z => ENNReal.ofReal (quotientAverageReal
      (mixedSubgroup F h) (mixedHaar F h) f z)) :=
    (ENNReal.continuous_ofReal.comp (continuous_quotientAverageReal _
      (isClosed_mixedSubgroup F h) _ f)).measurable
  have hLm : Measurable (fun q => ENNReal.ofReal (quotientAverageReal
      (lowerMixedSubgroup F h) (lowerMixedHaar F h) f q)) :=
    (ENNReal.continuous_ofReal.comp (continuous_quotientAverageReal _
      (isClosed_lowerMixedSubgroup F h) _ f)).measurable
  rw [Measure.lintegral_bind (radicalKernel F h μR).measurable.aemeasurable hMm.aemeasurable,
    ← lintegral_const_mul _ hLm]
  apply lintegral_congr
  intro q
  induction q using Quotient.inductionOn with
  | h g =>
    have hfm : Measurable (fun Z => radicalFiberPoint F h Z g) :=
      ((continuous_radicalFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    rw [radicalKernel_mk, lintegral_map hMm hfm]
    exact lintegral_radicalFiberPoint_quotientAverageReal F h μR f hf0 g

/-- Compatible quotient measures satisfy the full radical tower with the exact
supplied rectangular cube coefficient. -/
theorem radicalKernel_comp
    (μR : Measure R) [μR.IsAddHaarMeasure]
    (νL : Measure (LowerMixedQuotient F h))
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (lowerMixedHaar F h) νL)
    (νM : Measure (MixedQuotient F h))
    (hνM : IsCompatible (mixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (mixedHaar F h) νM) :
    radicalKernel F h μR ∘ₘ νL = μR {Z | ∀ i j, Z i j ∈ O} • νM := by
  let κ := radicalKernel F h μR
  let μG := generalLinearHaar F.Carrier t
  let μM := mixedHaar F h
  set c := μR {Z | ∀ i j, Z i j ∈ O}
  have hc : c ≠ ⊤ := (TwoBlockUnipotentQuotient.integerCube_mass_pos_lt_top F
    (m 1 + 1) (m 0 + 1) μR).2.ne
  have hL : ∀ f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ), (∀ y, 0 ≤ f y) →
      ∫⁻ z, ENNReal.ofReal (quotientAverageReal (mixedSubgroup F h) μM f z) ∂(κ ∘ₘ νL) =
        c * ∫⁻ y, ENNReal.ofReal (f y) ∂μG := fun f hf0 => by
    rw [lintegral_radicalKernel_comp_quotientAverageReal F h μR νL f hf0,
      RecursiveIntegration.lintegral_quotientAverageReal _ μG _ νL hνL f f.continuous f.hasCompactSupport hf0]
  have hR : ∀ f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ), (∀ y, 0 ≤ f y) →
      ∫⁻ z, ENNReal.ofReal (quotientAverageReal (mixedSubgroup F h) μM f z) ∂(c • νM) =
        c * ∫⁻ y, ENNReal.ofReal (f y) ∂μG := fun f hf0 => by
    rw [lintegral_smul_measure, smul_eq_mul,
      RecursiveIntegration.lintegral_quotientAverageReal _ μG _ νM hνM f f.continuous f.hasCompactSupport hf0]
  have hlift : ∀ φ : C_c(MixedQuotient F h, ℝ), (∀ q, 0 ≤ φ q) →
      ∃ f : C_c(GeneralLinear (t + 1) F.Carrier, ℝ), (∀ y, 0 ≤ f y) ∧
        ∀ q, quotientAverageReal (mixedSubgroup F h) μM f q = φ q := by
    intro φ hφ
    obtain ⟨f, hf, hf0⟩ := realQuotientPositiveLifting (mixedSubgroup F h)
      (isClosed_mixedSubgroup F h) μM φ
    refine ⟨f, hf0 hφ, fun q => ?_⟩
    induction q using Quotient.inductionOn with
    | h g => exact hf g
  have hfin : IsFiniteMeasureOnCompacts (κ ∘ₘ νL) := by
    refine ⟨fun C hC => ?_⟩
    obtain ⟨u, hu1, -, hucs, hu01⟩ :=
      exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
    let φ : C_c(MixedQuotient F h, ℝ) := ⟨u, hucs⟩
    obtain ⟨f, hf0, hfavg⟩ := hlift φ fun q => (hu01 q).1
    calc (κ ∘ₘ νL) C = ∫⁻ q, C.indicator 1 q ∂(κ ∘ₘ νL) :=
          (lintegral_indicator_one hC.isClosed.measurableSet).symm
      _ ≤ ∫⁻ q, ENNReal.ofReal (quotientAverageReal (mixedSubgroup F h) μM f q)
            ∂(κ ∘ₘ νL) := by
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
      _ = c * ∫⁻ y, ENNReal.ofReal (f y) ∂μG := hL f hf0
      _ < ⊤ := ENNReal.mul_lt_top hc.lt_top
          (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).lintegral_lt_top
  have : (κ ∘ₘ νL).Regular := inferInstance
  have : νM.Regular := hνM.regular
  have : (c • νM).Regular := Measure.Regular.smul hc
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro φ
  let φr : C_c(MixedQuotient F h, ℝ) :=
    ⟨⟨fun q => (φ q : ℝ), NNReal.continuous_coe.comp φ.continuous⟩,
      φ.hasCompactSupport.comp_left NNReal.coe_zero⟩
  obtain ⟨f, hf0, hfavg⟩ := hlift φr fun q => (φ q).coe_nonneg
  have key : ∀ μ' : Measure (MixedQuotient F h),
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal (mixedSubgroup F h) μM f q) ∂μ' =
        c * ∫⁻ y, ENNReal.ofReal (f y) ∂μG →
      ∫ q, (φ q : ℝ) ∂μ' = (c * ∫⁻ y, ENNReal.ofReal (f y) ∂μG).toReal := by
    intro μ' h'
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => (φ q).coe_nonneg)
      (NNReal.continuous_coe.comp φ.continuous).aestronglyMeasurable, ← h']
    congr 1
    apply lintegral_congr
    intro q
    rw [hfavg q]
    rfl
  rw [key _ (hL f hf0), key _ (hR f hf0)]

/-- The radical has determinant one, so the full tower restricts to every
matching determinant slice, including the zero outer slice in equation (2). -/
theorem radicalKernel_comp_restrict
    (μR : Measure R) [μR.IsAddHaarMeasure]
    (νL : Measure (LowerMixedQuotient F h))
    (νM : Measure (MixedQuotient F h))
    (hcomp : radicalKernel F h μR ∘ₘ νL =
      μR {Z | ∀ i j, Z i j ∈ O} • νM) (k : ℤ) :
    radicalKernel F h μR ∘ₘ νL.restrict (determinantSlice F h k) =
      μR {Z | ∀ i j, Z i j ∈ O} •
        νM.restrict (TwoBlockFirstBlockQuotient.determinantSlice F h k) := by
  let κ := radicalKernel F h μR
  let sL := determinantSlice F h k
  let sM := TwoBlockFirstBlockQuotient.determinantSlice F h k
  have hsL : MeasurableSet sL := measurableSet_determinantSlice F h k
  have hsM : MeasurableSet sM := TwoBlockFirstBlockQuotient.measurableSet_determinantSlice F h k
  have hpt : ∀ A, MeasurableSet A → ∀ q,
      κ q (A ∩ sM) = sL.indicator (fun q => κ q A) q := by
    intro A hA q
    induction q using Quotient.inductionOn with
    | h g =>
      have hfm : Measurable (fun Z => radicalFiberPoint F h Z g) :=
        ((continuous_radicalFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
      have hsupport : ∀ Z, radicalFiberPoint F h Z g ∈ sM ↔
          (Quotient.mk _ g : LowerMixedQuotient F h) ∈ sL := by
        intro Z
        exact (radicalFiberPoint_mem_determinantSlice_iff F h Z g k).trans
          (mk_mem_determinantSlice F h).symm
      rw [show κ (Quotient.mk _ g) = _ from radicalKernel_mk F h μR g,
        Measure.map_apply hfm (hA.inter hsM)]
      by_cases hg : (Quotient.mk _ g : LowerMixedQuotient F h) ∈ sL
      · rw [Set.indicator_of_mem hg,
          show κ (Quotient.mk _ g) = _ from radicalKernel_mk F h μR g,
          Measure.map_apply hfm hA]
        congr 1
        ext Z
        exact and_iff_left ((hsupport Z).2 hg)
      · rw [Set.indicator_of_notMem hg]
        have he : (fun Z => radicalFiberPoint F h Z g) ⁻¹' (A ∩ sM) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro Z hZ
          exact hg ((hsupport Z).1 hZ.2)
        rw [he, measure_empty]
  ext A hA
  change (κ ∘ₘ νL.restrict sL) A =
    (μR {Z | ∀ i j, Z i j ∈ O} • νM.restrict sM) A
  rw [Measure.bind_apply hA κ.measurable.aemeasurable, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hA, ← lintegral_indicator hsL]
  rw [show (∫⁻ q, sL.indicator (fun q => κ q A) q ∂νL) =
      ∫⁻ q, κ q (A ∩ sM) ∂νL from lintegral_congr fun q => (hpt A hA q).symm]
  rw [← Measure.bind_apply (hA.inter hsM) κ.measurable.aemeasurable, hcomp,
    Measure.smul_apply, smul_eq_mul]

/-- The full radical tower and all matching determinant-slice restrictions. -/
abbrev RadicalTowerStatement
    (μR : Measure R) [μR.IsAddHaarMeasure]
    (νL : Measure (LowerMixedQuotient F h)) (νM : Measure (MixedQuotient F h)) : Prop :=
  (radicalKernel F h μR ∘ₘ νL = μR {Z | ∀ i j, Z i j ∈ O} • νM) ∧
  ∀ k : ℤ, radicalKernel F h μR ∘ₘ νL.restrict (determinantSlice F h k) =
    μR {Z | ∀ i j, Z i j ∈ O} •
      νM.restrict (TwoBlockFirstBlockQuotient.determinantSlice F h k)

/-- Compatible measures satisfy the exact full and restricted radical tower. -/
theorem radicalTower
    (μR : Measure R) [μR.IsAddHaarMeasure]
    (νL : Measure (LowerMixedQuotient F h))
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (lowerMixedHaar F h) νL)
    (νM : Measure (MixedQuotient F h))
    (hνM : IsCompatible (mixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (mixedHaar F h) νM) :
    RadicalTowerStatement F h μR νL νM := by
  have hc := radicalKernel_comp F h μR νL hνL νM hνM
  exact ⟨hc, radicalKernel_comp_restrict F h μR νL νM hc⟩

end Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient
