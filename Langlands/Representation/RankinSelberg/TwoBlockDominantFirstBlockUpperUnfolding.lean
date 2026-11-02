import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockGlobalAnalysis

/-! # The actual global upper first-block unfolding -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory ProbabilityTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockFirstBlockQuotient TwoBlockLowerFirstBlockQuotient TwoBlockFirstBlockLaurent
  QuotientIntegration TwoBlockLowerUnipotentQuotient
open scoped ENNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance upperUnfoldingTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance upperUnfoldingValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance upperUnfoldingLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance upperUnfoldingT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance upperUnfoldingCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance upperUnfoldingGLTopology (a : ℕ) : IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a
local instance upperUnfoldingGLCountable (a : ℕ) : SecondCountableTopology (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology a
local instance upperUnfoldingMeasurable : MeasurableSpace F.Carrier := borel _
local instance upperUnfoldingBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance upperUnfoldingGLMeasurable (a : ℕ) : MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance upperUnfoldingGLBorel (a : ℕ) : BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance upperUnfoldingNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F.Carrier) := borel _
local instance upperUnfoldingNBorel (a : ℕ) : BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
local instance upperUnfoldingNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance upperUnfoldingNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance upperUnfoldingNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
variable (ν : AdditiveHaarMeasure F.Carrier)

local instance upperUnfoldingHQMeasurable :
    MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := borel _
local instance upperUnfoldingHQBorel :
    BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := ⟨rfl⟩
local instance upperUnfoldingHMeasurable :
    MeasurableSpace (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier) := borel _
local instance upperUnfoldingHBorel :
    BorelSpace (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier) := ⟨rfl⟩
local instance upperUnfoldingMixedSubgroupMeasurable :
    MeasurableSpace (mixedSubgroup F h) := borel _
local instance upperUnfoldingMixedSubgroupBorel : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance upperUnfoldingLowerMixedSubgroupMeasurable :
    MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance upperUnfoldingLowerMixedSubgroupBorel : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance upperUnfoldingMixedMeasurable :
    MeasurableSpace (MixedQuotient F h) := borel _
local instance upperUnfoldingMixedBorel : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance upperUnfoldingLowerMixedMeasurable :
    MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance upperUnfoldingLowerMixedBorel : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

/-- A representative-independent upper first-block average on the actual lower
mixed quotient, obtained by the two actual quotient averages. -/
def firstBlockUpperQuotientAverage
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
    (hInv : NormOneRightInvariant F (m 0) νA) (d : ℤ) :
    LowerMixedQuotient F h → ℂ :=
  radicalAverage F h (rectangularMeasure ν (m 1 + 1) (m 0 + 1))
    (TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInv d
      (rectangularSectionAverage F ell f j k Wtest ν
        (quotientDeterminantWeight F t (0 - ((j + k + 1 : ℕ) : ℂ) / 2))))

/-- The quotient average is measurable and integrable. The original raw norm
gives genuine triple-product convergence almost everywhere, where this average
equals the actual remaining-column integral of the upper coefficient. -/
theorem firstBlockUpperQuotientAverage_analysis
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (hσ : IsSmooth (σ 0))
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wmodel : (coefficientModel π lambda).toSubmodule)
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    [μR.IsAddHaarMeasure] (hraw : IsAbsIntegrable ψ (fun i => (ell i).val) μR f)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier)) [SigmaFinite νH]
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SigmaFinite νA]
    (νM : Measure (MixedQuotient F h)) (νL : Measure (LowerMixedQuotient F h))
    (hνN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN)
    (hνH : IsCompatible (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (TwoBlockUnipotentQuotient.blockHaar F.Carrier h) νH)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (hνM : IsCompatible (mixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (mixedHaar F h) νM)
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (lowerMixedHaar F h) νL) (d : ℤ) :
    let hInv := normOneRightInvariant_of_isCompatible F (m 0)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA hνA
    let Q := firstBlockUpperQuotientAverage F h j k ell f Wmodel.val ν νA hInv d
    let μZ := rectangularMeasure ν (m 1 + 1) (m 0 + 1)
    let μA := νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d)
    let μL := νL.restrict (TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)
    Measurable Q ∧ Integrable Q μL ∧
    (∀ᵐ qbase ∂μL, ∀ g : GeneralLinear (t + 1) F.Carrier, qbase = Quotient.mk _ g →
      Integrable (fun z :
          (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
            LeftUnipotentQuotient (m 0) F.Carrier) ×
              Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
        firstBlockUpperRowAverage F h j k ell f Wmodel.val ν 0 z.1.2 z.1.1 z.2 g)
        ((μZ.prod μA).prod (rectangularMeasure ν j (m 1 + 1))) ∧
      Q qbase = firstBlockUpperGlobalAverage F h j k ell f Wmodel.val ν νA d g) ∧
    (∫ q, Q q ∂μL) =
      (μZ {Z | ∀ i l, Z i l ∈ Valuation.integer
        (ValuativeRel.valuation F.Carrier)}).toReal •
      ∫ z, rectangularSectionAverage F ell f j k Wmodel.val ν
        (quotientDeterminantWeight F t (0 - ((j + k + 1 : ℕ) : ℂ) / 2)) z
        ∂νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h d) := by
  dsimp only
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  let hInv := normOneRightInvariant_of_isCompatible F (m 0)
    (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA hνA
  let weight := quotientDeterminantWeight F t (0 - ((j + k + 1 : ℕ) : ℂ) / 2)
  let E := rectangularSectionAverage F ell f j k Wmodel.val ν weight
  let B := TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInv d E
  let μZ := rectangularMeasure ν (m 1 + 1) (m 0 + 1)
  let μA := νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d)
  let μL := νL.restrict (TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)
  have hw : Continuous weight := quotientDeterminantWeight_continuous F t _
  have hreg := rectangularSectionIntegrand_regular F ell f j k π hπ lambda Wmodel ν weight hw
  have hfirst := rectangularSectionAverage_firstBlock_unfolding F ell f j k π hπ lambda
    Wmodel weight hw μR hraw ν νN νH νA νM hνN hνH hνA hνM d
  have hBm : Measurable B := hfirst.1
  have hBi : Integrable B
      (νM.restrict (TwoBlockFirstBlockQuotient.determinantSlice F h 0)) := hfirst.2.1
  have hQm : Measurable (radicalAverage F h μZ B) := by
    rw [radicalAverage_eq_integral_radicalKernel F h μZ B hBm]
    exact (hBm.stronglyMeasurable.integral_kernel
      (κ := radicalKernel F h μZ)).measurable
  obtain ⟨κR, hκR, _, _, _, hBo⟩ := radicalIntegration F h μZ νL hνL νM hνM
  obtain ⟨_, hQi, hQeq⟩ := (hBo B hBm).2 hBi
  have hnorm := rectangularSection_firstBlock_product_fibers F ell f j k π hπ lambda
    Wmodel weight hw μR hraw ν νN νH νA νM hνN hνH hνA hνM d
  have hNae := integrable_firstBlock_radical_product_ae F h
    (rectangularSectionNormProfile F ell f j k Wmodel.val ν weight) hnorm.1
    μZ νH νA νM νL hνH hνA hνM hνL d hnorm.2.1
  refine ⟨hQm, hQi, ?_, ?_⟩
  · filter_upwards [hNae] with qbase hq g hqg
    have hrect : ∀ᵐ z ∂μZ.prod μA, Integrable (fun x =>
        rectangularSectionIntegrand F ell f j k Wmodel.val weight x
          (fiberPoint h F.Carrier z.2 (lowerRadical h F.Carrier z.1 * g)))
          (rectangularMeasure ν j (t + 1)) :=
      Filter.Eventually.of_forall fun _ => hreg.2.1 _
    obtain ⟨hprod, he⟩ := firstBlockUpperRowAverage_joint_product_control F h j k ell f
      Wmodel.val ν (glModelFunction_continuous ψ _ π hπ.1.1 lambda Wmodel) hσ 0
      μZ μA g hrect (hq g hqg)
    refine ⟨hprod, ?_⟩
    subst qbase
    change radicalAverage F h μZ B (Quotient.mk _ g) = _
    rw [radicalAverage_mk]
    simp only [B, radicalFiberPoint_def, TwoBlockFirstBlockQuotient.firstBlockAverage_mk]
    exact he
  · exact hQeq.trans (congrArg (fun z : ℂ =>
      (μZ {Z | ∀ i l, Z i l ∈ Valuation.integer
        (ValuativeRel.valuation F.Carrier)}).toReal • z) hfirst.2.2.symm)

/-- Transposing the dimensions preserves the integral-cube mass of the
supplied scalar product Haar measure. -/
theorem rectangular_integerCube_mass_swap (a b : ℕ) :
    (rectangularMeasure ν a b)
      {Z | ∀ i l, Z i l ∈ Valuation.integer (ValuativeRel.valuation F.Carrier)} =
    (rectangularMeasure ν b a)
      {Z | ∀ i l, Z i l ∈ Valuation.integer (ValuativeRel.valuation F.Carrier)} := by
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  change
    (Measure.pi (fun _ : Fin a => Measure.pi (fun _ : Fin b => ν.measure)))
      {Z : Fin a → Fin b → F.Carrier |
        ∀ i l, Z i l ∈ Valuation.integer (ValuativeRel.valuation F.Carrier)} =
    (Measure.pi (fun _ : Fin b => Measure.pi (fun _ : Fin a => ν.measure)))
      {Z : Fin b → Fin a → F.Carrier |
        ∀ i l, Z i l ∈ Valuation.integer (ValuativeRel.valuation F.Carrier)}
  have hc (a b : ℕ) :
      {Z : Fin a → Fin b → F.Carrier |
        ∀ i l, Z i l ∈ Valuation.integer (ValuativeRel.valuation F.Carrier)} =
      Set.univ.pi (fun _ : Fin a => Set.univ.pi (fun _ : Fin b =>
        (Valuation.integer (ValuativeRel.valuation F.Carrier) : Set F.Carrier))) := by
    ext Z
    change (∀ i l, Z i l ∈ Valuation.integer (ValuativeRel.valuation F.Carrier)) ↔
      (∀ i ∈ Set.univ, ∀ l ∈ Set.univ,
        Z i l ∈ Valuation.integer (ValuativeRel.valuation F.Carrier))
    simp
  simp only [hc, Measure.pi_pi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [Nat.mul_comm]

/-- With the actual Jacquet realization and the supplied scalar product
measure, the upper quotient integral is exactly the original large JPSS
coefficient. The two integral-cube constants agree, so no rescaling remains. -/
theorem firstBlockUpperQuotientAverage_integral_eq_large
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (hσ : IsSmooth (σ 0))
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wmodel : (coefficientModel π lambda).toSubmodule)
    (Wjac : InverseWhittakerFunctions ψ t)
    (hjac : ∀ g : GeneralLinear (t + 1) F.Carrier,
      Wjac.val g = jacquetFunction ψ (fun i => (ell i).val)
        (rectangularMeasure ν (m 0 + 1) (m 1 + 1)) f g)
    (hraw : IsAbsIntegrable ψ (fun i => (ell i).val)
      (rectangularMeasure ν (m 0 + 1) (m 1 + 1)) f)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) [SigmaFinite νN]
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier)) [SigmaFinite νH]
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SigmaFinite νA]
    (νM : Measure (MixedQuotient F h)) (νL : Measure (LowerMixedQuotient F h))
    (hνN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN)
    (hνH : IsCompatible (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (TwoBlockUnipotentQuotient.blockHaar F.Carrier h) νH)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (hνM : IsCompatible (mixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (mixedHaar F h) νM)
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (lowerMixedHaar F h) νL) (d : ℤ) :
    let hInv := normOneRightInvariant_of_isCompatible F (m 0)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA hνA
    (∫ q, firstBlockUpperQuotientAverage F h j k ell f Wmodel.val ν νA hInv d q
      ∂νL.restrict (TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)) =
    ∫ q, ∫ X, unequalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
      j k Wmodel.val Wjac 0 X q ∂rectangularMeasure ν j (t + 1)
        ∂νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t d) := by
  dsimp only
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hu := firstBlockUpperQuotientAverage_analysis F h j k ell f ν π hπ hσ lambda Wmodel
    (rectangularMeasure ν (m 0 + 1) (m 1 + 1)) hraw
    νN νH νA νM νL hνN hνH hνA hνM hνL d
  have hl := rectangularSection_slice_unfolding F ell f
    (rectangularMeasure ν (m 0 + 1) (m 1 + 1)) Wjac hjac
    j k π hπ lambda Wmodel hraw ν νN νH hνN hνH d 0
  rw [hu.2.2.2]
  rw [rectangular_integerCube_mass_swap F ν (m 1 + 1) (m 0 + 1)]
  exact hl.2.2.symm

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
