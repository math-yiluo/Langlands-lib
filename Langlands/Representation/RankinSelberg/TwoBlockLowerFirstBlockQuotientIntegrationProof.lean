import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientIntegrationStatement
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasurePackage
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalAnalysis
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockSliceAnalysis
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockSliceTower

/-!
# Assembly of the linked lower mixed quotient disintegrations

The actual all-slice first-block measure tower supplies the remaining geometric
input. Its analytic consequences and the normalized radical tower assemble the
closed published proposition for every canonical field and positive block shape.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear QuotientIntegration
open scoped ENNReal ProbabilityTheory

universe uF

/-- The exact first-block analytic package needed by the final assembly. -/
def LowerFirstBlockIntegrationInputStatement : Prop :=
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
    let LQ0 := TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0
    let μG : Measure G := generalLinearHaar F.Carrier t
    let μGA : Measure GA := generalLinearHaar F.Carrier (m 0)
    let μNa : Measure Na := unipotentHaar F.Carrier (m 0)
    let μN : Measure N := unipotentHaar F.Carrier t
    let μHminus : Measure Hminus := Measure.map
      (TwoBlockLowerUnipotentQuotient.conjugationEquiv h F.Carrier).symm μN
    letI : μHminus.IsMulRightInvariant :=
      TwoBlockLowerFirstBlockQuotient.lowerHaar_isMulRightInvariant F h
    ∀ (νA : Measure AQ) (νL : Measure LQ) (νMinus : Measure HQ)
      (hA : IsCompatible Na μGA μNa νA),
      IsCompatible Lminus μG (TwoBlockLowerFirstBlockQuotient.lowerMixedHaar F h) νL →
      IsCompatible Hminus μG μHminus νMinus →
      let νL0 := νL.restrict LQ0
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

/-- The remaining geometric input, with exactly the fixed measures and slices. -/
def LowerFirstBlockSliceTowerInputStatement : Prop :=
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
    let LQ0 := TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0
    let μG : Measure G := generalLinearHaar F.Carrier t
    let μGA : Measure GA := generalLinearHaar F.Carrier (m 0)
    let μNa : Measure Na := unipotentHaar F.Carrier (m 0)
    let μN : Measure N := unipotentHaar F.Carrier t
    let μHminus : Measure Hminus := Measure.map
      (TwoBlockLowerUnipotentQuotient.conjugationEquiv h F.Carrier).symm μN
    letI : μHminus.IsMulRightInvariant :=
      TwoBlockLowerFirstBlockQuotient.lowerHaar_isMulRightInvariant F h
    ∀ (νA : Measure AQ) (νL : Measure LQ) (νMinus : Measure HQ) [SFinite νA]
      (hA : IsCompatible Na μGA μNa νA),
      IsCompatible Lminus μG (TwoBlockLowerFirstBlockQuotient.lowerMixedHaar F h) νL →
      IsCompatible Hminus μG μHminus νMinus →
      let νL0 := νL.restrict LQ0
    ∀ k : ℤ,
      let HQk := TwoBlockLowerUnipotentQuotient.determinantSlice F h k
      let νMinusk := νMinus.restrict HQk
      let d : ℝ≥0∞ := ENNReal.ofReal
        ((T.residueCardinality : ℝ) ^ (-(k * (b : ℤ))))
      let hInvariant :=
        TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible F (m 0)
          μGA μNa νA hA
      d • (TwoBlockLowerFirstBlockQuotient.firstBlockKernel F h νA hInvariant k ∘ₘ νL0) =
        νMinusk

/-- The complete first-block analytic input follows from the actual all-slice
measure tower; compatible small measures supply the required compact finiteness. -/
theorem lowerFirstBlockIntegrationInput_of_sliceTower
    (hTower : LowerFirstBlockSliceTowerInputStatement.{uF}) :
    LowerFirstBlockIntegrationInputStatement.{uF} := by
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
  let : SecondCountableTopology GA := T.generalLinearSecondCountableTopology a
  let : SecondCountableTopology (GeneralLinear b F.Carrier) :=
    T.generalLinearSecondCountableTopology b
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace GA := borel GA
  let : BorelSpace GA := ⟨rfl⟩
  let : MeasurableSpace A0 := borel A0
  let : BorelSpace A0 := ⟨rfl⟩
  let : SecondCountableTopology A0 := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : MeasurableSpace Na := borel Na
  let : BorelSpace Na := ⟨rfl⟩
  let : MeasurableSpace Nb := borel Nb
  let : BorelSpace Nb := ⟨rfl⟩
  let : SecondCountableTopology Nb := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let : MeasurableSpace Hminus := borel Hminus
  let : BorelSpace Hminus := ⟨rfl⟩
  let : MeasurableSpace Lminus := borel Lminus
  let : BorelSpace Lminus := ⟨rfl⟩
  -- Keep the actual rectangular and binary product measurable spaces.
  let : BorelSpace R := inferInstance
  let : BorelSpace (A0 × Nb) := inferInstance
  let : BorelSpace (R × (A0 × Nb)) := inferInstance
  let : MeasurableSpace MQ := borel MQ
  let : BorelSpace MQ := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let : MeasurableSpace LQ := borel LQ
  let : BorelSpace LQ := ⟨rfl⟩
  let : MeasurableSpace AQ := borel AQ
  let : BorelSpace AQ := ⟨rfl⟩
  let : MeasurableSpace NQ := borel NQ
  let : BorelSpace NQ := ⟨rfl⟩
  let (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
    T.generalLinearTopologicalGroup n
  let (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
  let (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
  let (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
    T.generalLinearSecondCountableTopology n
  let (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
    T.generalLinearLocallyCompactSpace n
  let (n : ℕ) : MeasurableSpace (upperUnipotent n F.Carrier) := borel _
  let (n : ℕ) : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
  dsimp only
  intro νA νL νMinus hA hL hMinus k
  let : νA.Regular := hA.regular
  let : SigmaFinite νA :=
    TwoBlockLowerFirstBlockQuotient.compatibleQuotient_sigmaFinite F (m 0) _
      (UpperUnipotent.isClosed (R := F.Carrier)) _ νA hA
  exact TwoBlockLowerFirstBlockQuotient.firstBlockSliceIntegration_of_comp F h
    νA _ νL νMinus k (hTower p F t m h νA νL νMinus hA hL hMinus k)

/-- All other clauses of the published target follow from the fixed normalized
measures and the already constructed zero-slice radical integration package. -/
theorem assembleLowerFirstBlockQuotientIntegration
    (hFirst : LowerFirstBlockIntegrationInputStatement.{uF}) :
    TwoBlockLowerFirstBlockQuotientIntegrationStatement.{uF} := by
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
  let : SecondCountableTopology GA := T.generalLinearSecondCountableTopology a
  let : SecondCountableTopology (GeneralLinear b F.Carrier) :=
    T.generalLinearSecondCountableTopology b
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace GA := borel GA
  let : BorelSpace GA := ⟨rfl⟩
  let : MeasurableSpace A0 := borel A0
  let : BorelSpace A0 := ⟨rfl⟩
  let : SecondCountableTopology A0 := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : MeasurableSpace Na := borel Na
  let : BorelSpace Na := ⟨rfl⟩
  let : MeasurableSpace Nb := borel Nb
  let : BorelSpace Nb := ⟨rfl⟩
  let : SecondCountableTopology Nb := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let : MeasurableSpace Hminus := borel Hminus
  let : BorelSpace Hminus := ⟨rfl⟩
  let : MeasurableSpace Lminus := borel Lminus
  let : BorelSpace Lminus := ⟨rfl⟩
  -- Keep the actual rectangular and binary product measurable spaces.
  let : BorelSpace R := inferInstance
  let : BorelSpace (A0 × Nb) := inferInstance
  let : BorelSpace (R × (A0 × Nb)) := inferInstance
  let : MeasurableSpace MQ := borel MQ
  let : BorelSpace MQ := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let : MeasurableSpace LQ := borel LQ
  let : BorelSpace LQ := ⟨rfl⟩
  let : MeasurableSpace AQ := borel AQ
  let : BorelSpace AQ := ⟨rfl⟩
  let : MeasurableSpace NQ := borel NQ
  let : BorelSpace NQ := ⟨rfl⟩
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
  let (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
    T.generalLinearTopologicalGroup n
  let (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
  let (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
  let (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
    T.generalLinearSecondCountableTopology n
  let (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
    T.generalLinearLocallyCompactSpace n
  let (n : ℕ) : MeasurableSpace (upperUnipotent n F.Carrier) := borel _
  let (n : ℕ) : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
  let (n : ℕ) : SecondCountableTopology (upperUnipotent n F.Carrier) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let (n : ℕ) : LocallyCompactSpace (upperUnipotent n F.Carrier) :=
    UpperUnipotent.locallyCompactSpace
  let : LocallyCompactSpace A0 :=
    (TwoBlockFirstBlockQuotient.isOpenEmbedding_normOneSubtype F a).locallyCompactSpace
  let : SecondCountableTopology M :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : LocallyCompactSpace M :=
    (TwoBlockFirstBlockQuotient.isClosed_mixedSubgroup F h).locallyCompactSpace
  dsimp only
  refine ⟨(TwoBlockLowerFirstBlockQuotient.continuous_projectionFromMixed F h).measurable,
    (TwoBlockLowerFirstBlockQuotient.continuous_projectionFromLower F h).measurable,
    (fun k => ⟨TwoBlockLowerFirstBlockQuotient.projectionFromMixed_preimage_determinantSlice F h k,
      TwoBlockLowerFirstBlockQuotient.projectionFromLower_preimage_determinantSlice F h k⟩),
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance,
    TwoBlockLowerFirstBlockQuotient.lowerHaar_isHaar F h,
    TwoBlockLowerFirstBlockQuotient.lowerHaar_regular F h,
    TwoBlockFirstBlockQuotient.normOneHaar F (m 0), inferInstance, inferInstance,
    TwoBlockFirstBlockQuotient.map_normOneHaar F (m 0),
    TwoBlockFirstBlockQuotient.mixedHaar_isHaar F h,
    TwoBlockFirstBlockQuotient.mixedHaar_regular F h,
    TwoBlockLowerFirstBlockQuotient.lowerMixedHaar F h, inferInstance, inferInstance,
    TwoBlockLowerFirstBlockQuotient.lowerMixedHaar_integral F h,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, TwoBlockFirstBlockQuotient.mixedHaar_isMulRightInvariant F h,
    TwoBlockLowerFirstBlockQuotient.lowerHaar_isMulRightInvariant F h,
    inferInstance, ?_⟩
  obtain ⟨hEx, hFin⟩ := TwoBlockLowerFirstBlockQuotient.measurePackage F h
  refine ⟨hEx.1, hEx.2.1, hEx.2.2.1, hEx.2.2.2, ?_, ?_⟩
  · intro μR _
    obtain ⟨hc0, hcT⟩ := TwoBlockUnipotentQuotient.integerCube_mass_pos_lt_top F
      (m 1 + 1) (m 0 + 1) μR
    exact ⟨hc0, hcT, TwoBlockLowerFirstBlockQuotient.lowerMixedProductMeasure_eq_smul F h μR⟩
  · intro νA νM νL νN hA hM hL hN
    obtain ⟨hσA, hσM, hσL, hσN, hMinus, hσMinus⟩ :=
      hFin νA νM νL νN hA hM hL hN
    refine ⟨hσA, hσM, hσL, hσN, hMinus, hσMinus, ?_, ?_⟩
    · intro μR _
      exact TwoBlockLowerFirstBlockQuotient.radicalIntegration F h μR νL hL νM hM
    · exact hFirst p F t m h νA νL _ hA hL hMinus

/-- The actual geometric tower discharges the all-slice input with the fixed
lower mixed Haar and the prescribed inverse-conjugation lower Haar. -/
theorem lowerFirstBlockSliceTowerInput : LowerFirstBlockSliceTowerInputStatement.{uF} := by
  intro p _ F t m h
  dsimp only
  intro νA νL νMinus _ hA hL hMinus k
  exact TwoBlockLowerFirstBlockQuotient.firstBlockKernel_comp_zeroSlice F h
    νA _ hA νL hL νMinus hMinus k

/-- The linked lower mixed quotient disintegrations of JPSS Section 4.9,
equations (2) and (8), with the exact published normalizations and slice laws. -/
theorem twoBlockLowerFirstBlockQuotientIntegration :
    TwoBlockLowerFirstBlockQuotientIntegrationStatement.{uF} :=
  assembleLowerFirstBlockQuotientIntegration
    (lowerFirstBlockIntegrationInput_of_sliceTower lowerFirstBlockSliceTowerInput)

end Langlands.RankinSelberg
