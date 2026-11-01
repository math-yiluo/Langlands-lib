import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientTower
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockFiberProper
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockKernelShift
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientAnalysis

/-!
# Normalized first-block quotient integration
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration
  TwoBlockFirstBlockQuotient
open scoped ENNReal

universe uF

/-- Normalized first-block disintegration over the fixed zero outer determinant slice,
with its s-finite measurable kernel and complete Tonelli and Bochner laws. -/
theorem twoBlockFirstBlockQuotientIntegration :
    TwoBlockFirstBlockQuotientIntegrationStatement.{uF} := by
  intro p _ F t m h
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let G := GeneralLinear (t + 1) F.Carrier
  let GA := GeneralLinear (m 0 + 1) F.Carrier
  let Na := upperUnipotent (m 0 + 1) F.Carrier
  let Nb := upperUnipotent (m 1 + 1) F.Carrier
  let A0 := normOneSubgroup F (m 0 + 1)
  let H := TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier
  let L := mixedSubgroup F h
  let AQ := LeftUnipotentQuotient (m 0) F.Carrier
  let HQ := TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier
  let LQ := MixedQuotient F h
  let : SecondCountableTopology GA := T.generalLinearSecondCountableTopology (m 0 + 1)
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace GA := borel GA
  let : BorelSpace GA := ⟨rfl⟩
  let : MeasurableSpace A0 := borel A0
  let : BorelSpace A0 := ⟨rfl⟩
  let : SecondCountableTopology A0 := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace L := borel L
  let : BorelSpace L := ⟨rfl⟩
  let : ∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F.Carrier) :=
    fun i => borel (upperUnipotent (m i + 1) F.Carrier)
  let : ∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F.Carrier) :=
    fun _ => ⟨rfl⟩
  let : ∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F.Carrier) :=
    fun i => by
      let := T.generalLinearSecondCountableTopology (m i + 1)
      exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : BorelSpace (TwoBlockUnipotentQuotient.BlockUnipotents m F.Carrier) := inferInstance
  let : BorelSpace (A0 × Nb) := inferInstance
  let : MeasurableSpace AQ := borel AQ
  let : BorelSpace AQ := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let : MeasurableSpace LQ := borel LQ
  let : BorelSpace LQ := ⟨rfl⟩
  let μG : Measure G := generalLinearHaar F.Carrier t
  let μGA : Measure GA := generalLinearHaar F.Carrier (m 0)
  let μNa : Measure Na := unipotentHaar F.Carrier (m 0)
  let μH : Measure H := TwoBlockUnipotentQuotient.blockHaar F.Carrier h
  change μH.IsHaarMeasure ∧ μH.Regular ∧ _
  refine ⟨inferInstance, inferInstance, normOneHaar F (m 0), inferInstance,
    inferInstance, map_normOneHaar F (m 0), ?_⟩
  let μL : Measure L := mixedHaar F h
  change μL.IsHaarMeasure ∧ μL.Regular ∧ _
  have hNa : Measure.IsMulRightInvariant μNa := inferInstance
  have hH : Measure.IsMulRightInvariant μH := inferInstance
  have hL : Measure.IsMulRightInvariant μL := inferInstance
  refine ⟨inferInstance, inferInstance, hNa, hH, hL, ?_⟩
  let := hNa
  let := hH
  let := hL
  refine ⟨TwoBlockUnipotentQuotient.fullUnipotent_compatibleMeasureExists F.Carrier (m 0),
    TwoBlockUnipotentQuotient.block_compatibleMeasureExists F.Carrier h,
    mixed_compatibleMeasureExists F h, ?_⟩
  intro νA νH νL hνA hνH hνL
  have hνA' : IsCompatible Na μGA μNa νA := hνA
  have hνH' : IsCompatible H μG μH νH := hνH
  have hνL' : IsCompatible L μG μL νL := hνL
  let := T.generalLinearLocallyCompactSpace (m 0 + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1)
  let := T.generalLinearSecondCountableTopology (t + 1)
  let := leftQuotient_locallyCompactSpace Na
  let := leftQuotient_locallyCompactSpace H
  let := leftQuotient_locallyCompactSpace L
  let := Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap Na)
  let := Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap H)
  let := Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap L)
  let := hνA'.regular
  let := hνH'.regular
  let := hνL'.regular
  have : SigmaFinite νA := inferInstance
  have : SigmaFinite νH := inferInstance
  have : SigmaFinite νL := inferInstance
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro k
  let hInvariant := normOneRightInvariant_of_isCompatible F (m 0) μGA μNa νA hνA'
  let κ := fiberKernel F h νA hInvariant k
  have hκfinite : IsSFiniteKernel κ := fiberKernel_isSFinite F h νA hInvariant k
  have hκ : ∀ g : G, κ (Quotient.mk _ g) =
      Measure.map (fun q => fiberPoint h F.Carrier q g)
        (νA.restrict (RankinSelberg.determinantSlice T (m 0) k)) :=
    fiberKernel_mk F h νA hInvariant k
  have hzero := (normalized_tower F h νA hInvariant hνA' νL hνL' νH hνH').2
  have hcomp : κ ∘ₘ νL.restrict (TwoBlockFirstBlockQuotient.determinantSlice F h 0) =
      νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h k) :=
    fiberKernel_comp_zeroSlice_eq F h νA hInvariant hνA' νL hνL' νH hzero k
  exact ⟨κ, hκfinite, hκ, hcomp,
    analytic_of_comp_eq F h νA hInvariant k κ hκ _ _ hcomp⟩

end Langlands.RankinSelberg
