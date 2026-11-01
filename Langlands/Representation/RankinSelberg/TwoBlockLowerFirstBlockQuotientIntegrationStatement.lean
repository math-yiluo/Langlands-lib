import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Group.GL.CountabilityProof
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Linked lower mixed quotient integration in JPSS Section 4.9

The measure disintegrations underlying equations (2) and (8), printed pages
416 and 418, share a Haar measure on the actual lower mixed subgroup, normalized
on its integral points. Every supplied rectangular Haar measure is retained:
its integral-cube mass occurs in equation (2). Equation (8) has the positive
density `|det v|^b`, constant on each small determinant slice, and no cube factor.
Kernel, normalization and absolute-integrability packaging are derived content.
This module states these assertions; it does not prove them.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear QuotientIntegration
open scoped ENNReal ProbabilityTheory

universe uF

/-- The two actual lower mixed quotient disintegrations of JPSS Section 4.9,
with one mass-one lower mixed Haar measure, compatible quotient existence and
transport from the full-unipotent quotient, measurable s-finite kernels, Tonelli,
absolute-integrability equivalences, and the Bochner laws for the published
unweighted descended averages. -/
def TwoBlockLowerFirstBlockQuotientIntegrationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1),
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.secondCountableTopology
    letI := T.generalLinearTopologicalGroup (t + 1)
    letI := T.generalLinearTopologicalGroup (m 0 + 1)
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    let a := m 0 + 1
    let b := m 1 + 1
    let G := GeneralLinear (t + 1) F.Carrier
    let GA := GeneralLinear a F.Carrier
    let A0 := TwoBlockFirstBlockQuotient.normOneSubgroup F a
    let Na := upperUnipotent a F.Carrier
    let Nb := upperUnipotent b F.Carrier
    let N := upperUnipotent (t + 1) F.Carrier
    let M := TwoBlockFirstBlockQuotient.mixedSubgroup F h
    let Hminus := TwoBlockLowerUnipotentQuotient.lowerBlockUnipotent h F.Carrier
    let Lminus := TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroup F h
    let MQ := TwoBlockFirstBlockQuotient.MixedQuotient F h
    let HQ := TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier
    let LQ := TwoBlockLowerFirstBlockQuotient.LowerMixedQuotient F h
    let AQ := LeftUnipotentQuotient (m 0) F.Carrier
    let NQ := LeftUnipotentQuotient t F.Carrier
    let R := Matrix (Fin b) (Fin a) F.Carrier
    letI : SecondCountableTopology GA := T.generalLinearSecondCountableTopology a
    letI : SecondCountableTopology (GeneralLinear b F.Carrier) :=
      T.generalLinearSecondCountableTopology b
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace GA := borel GA
    letI : BorelSpace GA := ⟨rfl⟩
    letI : MeasurableSpace A0 := borel A0
    letI : BorelSpace A0 := ⟨rfl⟩
    letI : SecondCountableTopology A0 := Topology.IsEmbedding.subtypeVal.secondCountableTopology
    letI : MeasurableSpace Na := borel Na
    letI : BorelSpace Na := ⟨rfl⟩
    letI : MeasurableSpace Nb := borel Nb
    letI : BorelSpace Nb := ⟨rfl⟩
    letI : SecondCountableTopology Nb := Topology.IsEmbedding.subtypeVal.secondCountableTopology
    letI : MeasurableSpace N := borel N
    letI : BorelSpace N := ⟨rfl⟩
    letI : MeasurableSpace M := borel M
    letI : BorelSpace M := ⟨rfl⟩
    letI : MeasurableSpace Hminus := borel Hminus
    letI : BorelSpace Hminus := ⟨rfl⟩
    letI : MeasurableSpace Lminus := borel Lminus
    letI : BorelSpace Lminus := ⟨rfl⟩
    -- Keep the actual rectangular and binary product measurable spaces.
    letI : BorelSpace R := inferInstance
    letI : BorelSpace (A0 × Nb) := inferInstance
    letI : BorelSpace (R × (A0 × Nb)) := inferInstance
    letI : MeasurableSpace MQ := borel MQ
    letI : BorelSpace MQ := ⟨rfl⟩
    letI : MeasurableSpace HQ := borel HQ
    letI : BorelSpace HQ := ⟨rfl⟩
    letI : MeasurableSpace LQ := borel LQ
    letI : BorelSpace LQ := ⟨rfl⟩
    letI : MeasurableSpace AQ := borel AQ
    letI : BorelSpace AQ := ⟨rfl⟩
    letI : MeasurableSpace NQ := borel NQ
    letI : BorelSpace NQ := ⟨rfl⟩
    let P_M := TwoBlockLowerFirstBlockQuotient.projectionFromMixed F h
    let P_H := TwoBlockLowerFirstBlockQuotient.projectionFromLower F h
    let LQ0 := TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0
    let MQ0 := TwoBlockFirstBlockQuotient.determinantSlice F h 0
    let μG : Measure G := generalLinearHaar F.Carrier t
    let μGA : Measure GA := generalLinearHaar F.Carrier (m 0)
    let μNa : Measure Na := unipotentHaar F.Carrier (m 0)
    let μNb : Measure Nb := unipotentHaar F.Carrier (m 1)
    let μN : Measure N := unipotentHaar F.Carrier t
    let μHminus : Measure Hminus := Measure.map
      (TwoBlockLowerUnipotentQuotient.conjugationEquiv h F.Carrier).symm μN
    Measurable P_M ∧ Measurable P_H ∧
    (∀ k : ℤ,
      P_M ⁻¹' TwoBlockLowerFirstBlockQuotient.determinantSlice F h k =
        TwoBlockFirstBlockQuotient.determinantSlice F h k ∧
      P_H ⁻¹' TwoBlockLowerFirstBlockQuotient.determinantSlice F h k =
        TwoBlockLowerUnipotentQuotient.determinantSlice F h k) ∧
    μG.IsHaarMeasure ∧ μG.Regular ∧ μGA.IsHaarMeasure ∧ μGA.Regular ∧
    μNa.IsHaarMeasure ∧ μNa.Regular ∧ μNb.IsHaarMeasure ∧ μNb.Regular ∧
    μN.IsHaarMeasure ∧ μN.Regular ∧ μHminus.IsHaarMeasure ∧ μHminus.Regular ∧
    ∃ μA0 : Measure A0, μA0.IsHaarMeasure ∧ μA0.Regular ∧
      Measure.map Subtype.val μA0 = μGA.restrict (A0 : Set GA) ∧
      let μM : Measure M := Measure.map
        (TwoBlockFirstBlockQuotient.mixedSubgroupEquiv F h) (μA0.prod μNb)
      μM.IsHaarMeasure ∧ μM.Regular ∧
      ∃ μL : Measure Lminus, μL.IsHaarMeasure ∧ μL.Regular ∧
        μL (Subtype.val ⁻¹'
          (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer t :
            Set G)) = 1 ∧
        ∃ (hG : Measure.IsMulRightInvariant μG)
          (hGA : Measure.IsMulRightInvariant μGA)
          (hNa : Measure.IsMulRightInvariant μNa)
          (hNb : Measure.IsMulRightInvariant μNb)
          (hN : Measure.IsMulRightInvariant μN)
          (hA0 : Measure.IsMulRightInvariant μA0)
          (hM : Measure.IsMulRightInvariant μM)
          (hHminus : Measure.IsMulRightInvariant μHminus)
          (hL : Measure.IsMulRightInvariant μL),
          letI := hG
          letI := hGA
          letI := hNa
          letI := hNb
          letI := hN
          letI := hA0
          letI := hM
          letI := hHminus
          letI := hL
          (∃ νA : Measure AQ, IsCompatible Na μGA μNa νA) ∧
          (∃ νM : Measure MQ, IsCompatible M μG μM νM) ∧
          (∃ νL : Measure LQ, IsCompatible Lminus μG μL νL) ∧
          (∃ νN : Measure NQ, IsCompatible N μG μN νN) ∧
          (∀ (μR : Measure R) [μR.IsAddHaarMeasure],
            let O := (ValuativeRel.valuation F.Carrier).integer
            let c : ℝ≥0∞ := μR {Z | ∀ i j, Z i j ∈ O}
            0 < c ∧ c < ⊤ ∧
              Measure.map
                (TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroupHomeomorph F h)
                (μR.prod (μA0.prod μNb)) = c • μL) ∧
          ∀ (νA : Measure AQ) (νM : Measure MQ) (νL : Measure LQ) (νN : Measure NQ)
            (hA : IsCompatible Na μGA μNa νA),
            IsCompatible M μG μM νM → IsCompatible Lminus μG μL νL →
            IsCompatible N μG μN νN →
            let νMinus : Measure HQ := Measure.map
              (TwoBlockLowerUnipotentQuotient.lowerToStandard h F.Carrier).symm νN
            let νL0 := νL.restrict LQ0
            SigmaFinite νA ∧ SigmaFinite νM ∧ SigmaFinite νL ∧ SigmaFinite νN ∧
            IsCompatible Hminus μG μHminus νMinus ∧ SigmaFinite νMinus ∧
            (∀ (μR : Measure R) [μR.IsAddHaarMeasure],
              let O := (ValuativeRel.valuation F.Carrier).integer
              let c : ℝ≥0∞ := μR {Z | ∀ i j, Z i j ∈ O}
              let νM0 := νM.restrict MQ0
              ∃ (κR : ProbabilityTheory.Kernel LQ MQ)
                (_hκR : ProbabilityTheory.IsSFiniteKernel κR),
                (∀ g : G, κR (Quotient.mk _ g) =
                  Measure.map
                    (fun Z => TwoBlockLowerFirstBlockQuotient.radicalFiberPoint F h Z g) μR) ∧
                (κR ∘ₘ νL0 = c • νM0) ∧
                (∀ f : MQ → ℝ≥0∞, Measurable f →
                  (∫⁻ q, ∫⁻ z, f z ∂κR q ∂νL0) = c * ∫⁻ z, f z ∂νM0) ∧
                (∀ f : MQ → ℂ, Measurable f →
                  (Integrable f νM0 ↔
                    (∀ᵐ q ∂νL0, Integrable f (κR q)) ∧
                    Integrable (fun q => ∫ z, ‖f z‖ ∂κR q) νL0) ∧
                  (Integrable f νM0 →
                    AEStronglyMeasurable
                      (TwoBlockLowerFirstBlockQuotient.radicalAverage F h μR f) νL0 ∧
                    Integrable
                      (TwoBlockLowerFirstBlockQuotient.radicalAverage F h μR f) νL0 ∧
                    (∫ q, TwoBlockLowerFirstBlockQuotient.radicalAverage F h μR f q ∂νL0) =
                      c.toReal • ∫ z, f z ∂νM0))) ∧
            ∀ k : ℤ,
              let AQk := RankinSelberg.determinantSlice T (m 0) k
              let HQk := TwoBlockLowerUnipotentQuotient.determinantSlice F h k
              let νMinusk := νMinus.restrict HQk
              let d : ℝ≥0∞ := ENNReal.ofReal
                ((T.residueCardinality : ℝ) ^ (-(k * (b : ℤ))))
              let hInvariant :=
                TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible F (m 0)
                  μGA μNa νA hA
              0 < d ∧ d < ⊤ ∧
              (∀ v : GA, (Quotient.mk _ v : AQ) ∈ AQk →
                d = (ENNReal.ofReal (T.normalizedAbs
                  (GeneralLinear.determinant v : F.Carrier))) ^ b) ∧
              ∃ (κA : ProbabilityTheory.Kernel LQ HQ)
                (_hκA : ProbabilityTheory.IsSFiniteKernel κA),
                (∀ g : G, κA (Quotient.mk _ g) =
                  Measure.map
                    (fun q => TwoBlockLowerFirstBlockQuotient.firstBlockFiberPoint F h q g)
                    (νA.restrict AQk)) ∧
                (d • (κA ∘ₘ νL0) = νMinusk) ∧
                (∀ f : HQ → ℝ≥0∞, Measurable f →
                  (∫⁻ z, f z ∂νMinusk) =
                    d * ∫⁻ q, ∫⁻ z, f z ∂κA q ∂νL0) ∧
                (∀ f : HQ → ℂ, Measurable f →
                  (Integrable f νMinusk ↔
                    (∀ᵐ q ∂νL0, Integrable f (κA q)) ∧
                    Integrable (fun q => ∫ z, ‖f z‖ ∂κA q) νL0) ∧
                  (Integrable f νMinusk →
                    AEStronglyMeasurable
                      (TwoBlockLowerFirstBlockQuotient.firstBlockAverage
                        F h νA hInvariant k f) νL0 ∧
                    Integrable
                      (TwoBlockLowerFirstBlockQuotient.firstBlockAverage
                        F h νA hInvariant k f) νL0 ∧
                    (∫ z, f z ∂νMinusk) = d.toReal •
                      ∫ q, TwoBlockLowerFirstBlockQuotient.firstBlockAverage
                        F h νA hInvariant k f q ∂νL0))

end Langlands.RankinSelberg
