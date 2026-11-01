import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalTower
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientAnalysis

/-!
# Analytic laws for the lower mixed radical tower

The exact zero-slice measure identity gives the Tonelli and Bochner laws for the
published unweighted average, together with genuine absolute integrability.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
open scoped ENNReal CompactlySupported ProbabilityTheory

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerRadicalAnalysisInstance01 : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance lowerRadicalAnalysisInstance02 : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance lowerRadicalAnalysisInstance03 : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance lowerRadicalAnalysisInstance04 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance lowerRadicalAnalysisInstance05 : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance lowerRadicalAnalysisInstance06 : MeasurableSpace F.Carrier := borel _
local instance lowerRadicalAnalysisInstance07 : BorelSpace F.Carrier := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance08 (a b : ℕ) : LocallyCompactSpace (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F.Carrier))
local instance lowerRadicalAnalysisInstance09 (a b : ℕ) : SecondCountableTopology (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F.Carrier))
local instance lowerRadicalAnalysisInstance10 (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n
local instance lowerRadicalAnalysisInstance11 (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance lowerRadicalAnalysisInstance12 (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance13 (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance lowerRadicalAnalysisInstance14 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance lowerRadicalAnalysisInstance15 (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance lowerRadicalAnalysisInstance16 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance17 (n : ℕ) : SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerRadicalAnalysisInstance18 (n : ℕ) : LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance lowerRadicalAnalysisInstance19 (n : ℕ) : MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance lowerRadicalAnalysisInstance20 (n : ℕ) : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance21 (n : ℕ) : SecondCountableTopology (upperUnipotent n F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerRadicalAnalysisInstance22 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F.Carrier) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerRadicalAnalysisInstance23 : MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance lowerRadicalAnalysisInstance24 : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance25 : SecondCountableTopology (lowerMixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerRadicalAnalysisInstance26 : LocallyCompactSpace (lowerMixedSubgroup F h) :=
  (isClosed_lowerMixedSubgroup F h).locallyCompactSpace

local notation "R" => Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier
local notation "D" => normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier
local notation "μD" => Measure.prod (normOneHaar F (m 0)) (unipotentHaar F.Carrier (m 1))


local instance lowerRadicalAnalysisInstance27 : MeasurableSpace (mixedSubgroup F h) := borel _
local instance lowerRadicalAnalysisInstance28 : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance29 : SecondCountableTopology (mixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerRadicalAnalysisInstance30 : LocallyCompactSpace (mixedSubgroup F h) :=
  (isClosed_mixedSubgroup F h).locallyCompactSpace
local instance lowerRadicalAnalysisInstance31 : MeasurableSpace (MixedQuotient F h) := borel _
local instance lowerRadicalAnalysisInstance32 : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance lowerRadicalAnalysisInstance33 : T2Space (MixedQuotient F h) :=
  leftQuotient_t2Space _ (isClosed_mixedSubgroup F h)
local instance lowerRadicalAnalysisInstance34 : LocallyCompactSpace (MixedQuotient F h) := leftQuotient_locallyCompactSpace _
local instance lowerRadicalAnalysisInstance35 : SecondCountableTopology (MixedQuotient F h) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
local instance lowerRadicalAnalysisInstance36 : MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance lowerRadicalAnalysisInstance37 : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

local notation "O" => Valuation.integer (ValuativeRel.valuation F.Carrier)

/-- The published unweighted radical average is the actual kernel integral
at every lower mixed quotient point. -/
theorem radicalAverage_eq_integral_radicalKernel
    (μR : Measure R) [μR.IsAddHaarMeasure]
    (f : MixedQuotient F h → ℂ) (hf : Measurable f) :
    radicalAverage F h μR f = fun q => ∫ z, f z ∂radicalKernel F h μR q := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    have hfm : Measurable (fun Z => radicalFiberPoint F h Z g) :=
      ((continuous_radicalFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    rw [radicalAverage_mk, radicalKernel_mk,
      integral_map hfm.aemeasurable hf.aestronglyMeasurable]

/-- The complete equation (2) conclusions on the required zero slices. -/
abbrev RadicalIntegrationStatement
    (μR : Measure R) [μR.IsAddHaarMeasure]
    (νL : Measure (LowerMixedQuotient F h)) (νM : Measure (MixedQuotient F h)) : Prop :=
  let c := μR {Z | ∀ i j, Z i j ∈ O}
  let νL0 := νL.restrict (determinantSlice F h 0)
  let νM0 := νM.restrict (TwoBlockFirstBlockQuotient.determinantSlice F h 0)
  ∃ (κR : Kernel (LowerMixedQuotient F h) (MixedQuotient F h))
    (_hκR : IsSFiniteKernel κR),
    (∀ g : GeneralLinear (t + 1) F.Carrier, κR (Quotient.mk _ g) =
      Measure.map (fun Z => radicalFiberPoint F h Z g) μR) ∧
    (κR ∘ₘ νL0 = c • νM0) ∧
    (∀ f : MixedQuotient F h → ℝ≥0∞, Measurable f →
      (∫⁻ q, ∫⁻ z, f z ∂κR q ∂νL0) = c * ∫⁻ z, f z ∂νM0) ∧
    (∀ f : MixedQuotient F h → ℂ, Measurable f →
      (Integrable f νM0 ↔
        (∀ᵐ q ∂νL0, Integrable f (κR q)) ∧
        Integrable (fun q => ∫ z, ‖f z‖ ∂κR q) νL0) ∧
      (Integrable f νM0 →
        AEStronglyMeasurable (radicalAverage F h μR f) νL0 ∧
        Integrable (radicalAverage F h μR f) νL0 ∧
        (∫ q, radicalAverage F h μR f q ∂νL0) =
          c.toReal • ∫ z, f z ∂νM0))

/-- The scaled measure tower gives the full Tonelli, absolute-integrability
and Bochner conclusions for the supplied rectangular Haar and zero outer slice. -/
theorem radicalIntegration
    (μR : Measure R) [μR.IsAddHaarMeasure]
    (νL : Measure (LowerMixedQuotient F h))
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (lowerMixedHaar F h) νL)
    (νM : Measure (MixedQuotient F h))
    (hνM : IsCompatible (mixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (mixedHaar F h) νM) :
    RadicalIntegrationStatement F h μR νL νM := by
  have hc := TwoBlockUnipotentQuotient.integerCube_mass_pos_lt_top F
    (m 1 + 1) (m 0 + 1) μR
  have hcomp := (radicalTower F h μR νL hνL νM hνM).2 0
  refine ⟨radicalKernel F h μR, radicalKernel_isSFinite F h μR,
    radicalKernel_mk F h μR, hcomp, ?_, ?_⟩
  · intro f hf
    exact TwoBlockUnipotentQuotient.lintegral_lintegral_of_comp_eq_smul hcomp hf
  · intro f hf
    refine ⟨TwoBlockUnipotentQuotient.integrable_iff_of_comp_eq_smul
      hcomp hc.1.ne' hc.2.ne hf.aestronglyMeasurable, ?_⟩
    intro hfi
    rw [radicalAverage_eq_integral_radicalKernel F h μR f hf]
    obtain ⟨hi, he⟩ := TwoBlockUnipotentQuotient.integral_integral_of_comp_eq_smul
      hcomp hc.2.ne hfi
    exact ⟨hi.aestronglyMeasurable, hi, he⟩

end Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient
