import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockFiberProper
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockDensity
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientAnalysis

/-!
# Analytic consequences of the lower first-block slice tower

The exact density-scaled slice measure identity is an explicit premise here.
It implies the complete analytic laws for the actual unweighted average.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
open scoped ENNReal CompactlySupported ProbabilityTheory

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerSliceAnalysisInstance01 : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance lowerSliceAnalysisInstance02 : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance lowerSliceAnalysisInstance03 : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance lowerSliceAnalysisInstance04 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance lowerSliceAnalysisInstance05 : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance lowerSliceAnalysisInstance06 : MeasurableSpace F.Carrier := borel _
local instance lowerSliceAnalysisInstance07 : BorelSpace F.Carrier := ⟨rfl⟩
local instance lowerSliceAnalysisInstance08 (a b : ℕ) : LocallyCompactSpace (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin b → Fin a → F.Carrier))
local instance lowerSliceAnalysisInstance09 (a b : ℕ) : SecondCountableTopology (Matrix (Fin b) (Fin a) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin b → Fin a → F.Carrier))
local instance lowerSliceAnalysisInstance10 (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n
local instance lowerSliceAnalysisInstance11 (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance lowerSliceAnalysisInstance12 (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance13 (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance lowerSliceAnalysisInstance14 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance lowerSliceAnalysisInstance15 (n : ℕ) : MeasurableSpace (normOneSubgroup F n) := borel _
local instance lowerSliceAnalysisInstance16 (n : ℕ) : BorelSpace (normOneSubgroup F n) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance17 (n : ℕ) : SecondCountableTopology (normOneSubgroup F n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceAnalysisInstance18 (n : ℕ) : LocallyCompactSpace (normOneSubgroup F n) :=
  (isOpenEmbedding_normOneSubtype F n).locallyCompactSpace
local instance lowerSliceAnalysisInstance19 (n : ℕ) : MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance lowerSliceAnalysisInstance20 (n : ℕ) : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance21 (n : ℕ) : SecondCountableTopology (upperUnipotent n F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceAnalysisInstance22 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F.Carrier) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerSliceAnalysisInstance23 : MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance lowerSliceAnalysisInstance24 : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance25 : SecondCountableTopology (lowerMixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceAnalysisInstance26 : LocallyCompactSpace (lowerMixedSubgroup F h) :=
  (isClosed_lowerMixedSubgroup F h).locallyCompactSpace

local notation "R" => Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier
local notation "D" => normOneSubgroup F (m 0 + 1) × upperUnipotent (m 1 + 1) F.Carrier
local notation "μD" => Measure.prod (normOneHaar F (m 0)) (unipotentHaar F.Carrier (m 1))


local instance lowerSliceAnalysisInstance27 : MeasurableSpace (mixedSubgroup F h) := borel _
local instance lowerSliceAnalysisInstance28 : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance29 : SecondCountableTopology (mixedSubgroup F h) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerSliceAnalysisInstance30 : LocallyCompactSpace (mixedSubgroup F h) :=
  (isClosed_mixedSubgroup F h).locallyCompactSpace
local instance lowerSliceAnalysisInstance31 : MeasurableSpace (MixedQuotient F h) := borel _
local instance lowerSliceAnalysisInstance32 : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance33 : T2Space (MixedQuotient F h) :=
  leftQuotient_t2Space _ (isClosed_mixedSubgroup F h)
local instance lowerSliceAnalysisInstance34 : LocallyCompactSpace (MixedQuotient F h) := leftQuotient_locallyCompactSpace _
local instance lowerSliceAnalysisInstance35 : SecondCountableTopology (MixedQuotient F h) :=
  Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
local instance lowerSliceAnalysisInstance36 : MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance lowerSliceAnalysisInstance37 : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

local instance lowerSliceAnalysisInstance38 (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance lowerSliceAnalysisInstance39 (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance lowerSliceAnalysisInstance40 :
    MeasurableSpace (LowerQuotient h F.Carrier) := borel _
local instance lowerSliceAnalysisInstance41 :
    BorelSpace (LowerQuotient h F.Carrier) := ⟨rfl⟩

/-- The published unweighted first-block slice average is the actual kernel
integral at every lower mixed quotient point. -/
theorem firstBlockAverage_eq_integral_firstBlockKernel
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
    (hνA : NormOneRightInvariant F (m 0) νA) (k : ℤ)
    (f : LowerQuotient h F.Carrier → ℂ) (hf : Measurable f) :
    firstBlockAverage F h νA hνA k f =
      fun q => ∫ z, f z ∂firstBlockKernel F h νA hνA k q := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    have hfm : Measurable (fun z => firstBlockFiberPoint F h z g) :=
      ((continuous_firstBlockFiberPoint F h).comp
        (continuous_id.prodMk continuous_const)).measurable
    rw [firstBlockAverage_mk, firstBlockKernel_mk,
      integral_map hfm.aemeasurable hf.aestronglyMeasurable]

/-- The complete first-block conclusions on one small determinant slice and
the zero outer slice. -/
abbrev FirstBlockSliceIntegrationStatement
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
    (hνA : NormOneRightInvariant F (m 0) νA)
    (νL : Measure (LowerMixedQuotient F h))
    (νMinus : Measure (LowerQuotient h F.Carrier)) (k : ℤ) : Prop :=
  let T := F.canonicalTopologicalData
  let b := m 1 + 1
  let AQk := RankinSelberg.determinantSlice T (m 0) k
  let νL0 := νL.restrict (determinantSlice F h 0)
  let νMinusk := νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)
  let d : ℝ≥0∞ := ENNReal.ofReal ((T.residueCardinality : ℝ) ^ (-(k * (b : ℤ))))
  0 < d ∧ d < ⊤ ∧
  (∀ v : GeneralLinear (m 0 + 1) F.Carrier,
    (Quotient.mk _ v : LeftUnipotentQuotient (m 0) F.Carrier) ∈ AQk →
      d = (ENNReal.ofReal (T.normalizedAbs
        (GeneralLinear.determinant v : F.Carrier))) ^ b) ∧
  ∃ (κA : Kernel (LowerMixedQuotient F h) (LowerQuotient h F.Carrier))
    (_hκA : IsSFiniteKernel κA),
    (∀ g : GeneralLinear (t + 1) F.Carrier, κA (Quotient.mk _ g) =
      Measure.map (fun q => firstBlockFiberPoint F h q g) (νA.restrict AQk)) ∧
    (d • (κA ∘ₘ νL0) = νMinusk) ∧
    (∀ f : LowerQuotient h F.Carrier → ℝ≥0∞, Measurable f →
      (∫⁻ z, f z ∂νMinusk) = d * ∫⁻ q, ∫⁻ z, f z ∂κA q ∂νL0) ∧
    (∀ f : LowerQuotient h F.Carrier → ℂ, Measurable f →
      (Integrable f νMinusk ↔
        (∀ᵐ q ∂νL0, Integrable f (κA q)) ∧
        Integrable (fun q => ∫ z, ‖f z‖ ∂κA q) νL0) ∧
      (Integrable f νMinusk →
        AEStronglyMeasurable (firstBlockAverage F h νA hνA k f) νL0 ∧
        Integrable (firstBlockAverage F h νA hνA k f) νL0 ∧
        (∫ z, f z ∂νMinusk) = d.toReal •
          ∫ q, firstBlockAverage F h νA hνA k f q ∂νL0))

/-- The exact density-scaled slice tower implies Tonelli, genuine absolute
integrability, and the Bochner law for the actual first-block slice average. -/
theorem firstBlockSliceIntegration_of_comp
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
    [IsFiniteMeasureOnCompacts νA] (hνA : NormOneRightInvariant F (m 0) νA)
    (νL : Measure (LowerMixedQuotient F h))
    (νMinus : Measure (LowerQuotient h F.Carrier)) (k : ℤ)
    (hcomp : ENNReal.ofReal
      ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ)))) •
        (firstBlockKernel F h νA hνA k ∘ₘ νL.restrict (determinantSlice F h 0)) =
      νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) :
    FirstBlockSliceIntegrationStatement F h νA hνA νL νMinus k := by
  obtain ⟨hd0, hdT, hdet⟩ := firstBlockDensity F (m 0) (m 1 + 1) k
  let : IsSFiniteKernel (firstBlockKernel F h νA hνA k) :=
    firstBlockKernel_isSFinite F h νA hνA k
  refine ⟨hd0, hdT, hdet, firstBlockKernel F h νA hνA k, inferInstance,
    firstBlockKernel_mk F h νA hνA k, hcomp, ?_, ?_⟩
  · intro f hf
    rw [← hcomp, lintegral_smul_measure,
      Measure.lintegral_bind (firstBlockKernel F h νA hνA k).measurable.aemeasurable
        hf.aemeasurable]
    rfl
  · intro f hf
    refine ⟨?_, ?_⟩
    · rw [← hcomp, integrable_smul_measure hd0.ne' hdT.ne]
      exact Measure.integrable_comp_iff hf.aestronglyMeasurable
    · intro hfi
      rw [firstBlockAverage_eq_integral_firstBlockKernel F h νA hνA k f hf]
      have hfiComp : Integrable f
          (firstBlockKernel F h νA hνA k ∘ₘ νL.restrict (determinantSlice F h 0)) := by
        apply (integrable_smul_measure hd0.ne' hdT.ne).mp
        rwa [hcomp]
      rw [Measure.comp_eq_comp_const_apply] at hfiComp
      have hi : Integrable (fun q => ∫ z, f z ∂firstBlockKernel F h νA hνA k q)
          (νL.restrict (determinantSlice F h 0)) := by
        simpa using hfiComp.integral_comp
      refine ⟨hi.aestronglyMeasurable, hi, ?_⟩
      rw [← hcomp, integral_smul_measure, Measure.comp_eq_comp_const_apply,
        Kernel.integral_comp hfiComp]
      simp

end Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient
