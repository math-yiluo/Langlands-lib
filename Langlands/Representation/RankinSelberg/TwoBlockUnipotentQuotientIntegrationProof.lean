import Langlands.Representation.RankinSelberg.TwoBlockUnipotentMeasures
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentFiberProper
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientTower
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientAnalysis

/-!
# Normalized integration for the two-block unipotent quotient
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory ProbabilityTheory GeneralLinear QuotientIntegration
  TwoBlockUnipotentQuotient TwoBlockUnipotentQuotientIntegration
open scoped ENNReal

universe uF

/-- The normalized quotient tower and its Tonelli and Bochner consequences,
for the actual two-block radical kernel and every supplied rectangular Haar. -/
theorem twoBlockUnipotentQuotientIntegration :
    TwoBlockUnipotentQuotientIntegrationStatement.{uF} := by
  intro p _ F t m h
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1)
  let := T.generalLinearSecondCountableTopology (t + 1)
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let G := GeneralLinear (t + 1) F.Carrier
  let N := upperUnipotent (t + 1) F.Carrier
  let H := blockUnipotent h F.Carrier
  let NQ := LeftUnipotentQuotient t F.Carrier
  let HQ := BlockQuotient h F.Carrier
  let R := Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : ∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F.Carrier) :=
    fun i => borel (upperUnipotent (m i + 1) F.Carrier)
  let : ∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F.Carrier) :=
    fun _ => ⟨rfl⟩
  let : ∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F.Carrier) :=
    fun i => by
      let := T.generalLinearSecondCountableTopology (m i + 1)
      exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : BorelSpace (BlockUnipotents m F.Carrier) := inferInstance
  let : BorelSpace R := inferInstance
  let : MeasurableSpace NQ := borel NQ
  let : BorelSpace NQ := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let μG : Measure G := generalLinearHaar F.Carrier t
  let μN : Measure N := unipotentHaar F.Carrier t
  let μH : Measure H := blockHaar F.Carrier h
  change μH.IsHaarMeasure ∧ μH.Regular ∧ _
  have hN : Measure.IsMulRightInvariant μN := inferInstance
  have hH : Measure.IsMulRightInvariant μH := inferInstance
  refine ⟨inferInstance, inferInstance, hN, hH, ?_⟩
  let := hN
  let := hH
  refine ⟨fullUnipotent_compatibleMeasureExists F.Carrier t,
    block_compatibleMeasureExists F.Carrier h, ?_⟩
  intro μR _
  obtain ⟨hc0, hc⟩ := integerCube_mass_pos_lt_top F (m 0 + 1) (m 1 + 1) μR
  let c : ℝ≥0∞ := μR {x | ∀ a b, x a b ∈ (ValuativeRel.valuation F.Carrier).integer}
  let κ := fiberKernel F h μR
  have : IsSFiniteKernel κ := fiberKernel_isSFinite F h μR
  have hκ : ∀ g : G, κ (Quotient.mk _ g) =
      Measure.map (fun x => fiberPoint h F.Carrier x g) μR :=
    fiberKernel_mk F h μR
  refine ⟨hc0, hc, κ, inferInstance, hκ, ?_⟩
  intro νN νH hνN hνH
  have hνN' : IsCompatible N μG μN νN := hνN
  have hνH' : IsCompatible H μG μH νH := hνH
  let := leftQuotient_locallyCompactSpace N
  let := leftQuotient_locallyCompactSpace H
  let := Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap N)
  let := Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap H)
  let := hνN'.regular
  let := hνH'.regular
  have : SigmaFinite νN := inferInstance
  have : SigmaFinite νH := inferInstance
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hwhole : κ ∘ₘ νN = c • νH :=
    comp_eq_smul h μG μH (blockMeasure_integral F.Carrier h) μR hc.ne κ hκ
      νN hνN' νH hνH'
  intro s hs
  have hrestricted := comp_restrict_eq_smul h μR κ hκ νN νH c hwhole s hs
  exact ⟨hrestricted,
    analytic_of_comp_eq_smul F h μR c hc0.ne' hc.ne κ hκ
      (νN.restrict s) (νH.restrict (projection h F.Carrier ⁻¹' s)) hrestricted⟩

end Langlands.RankinSelberg
