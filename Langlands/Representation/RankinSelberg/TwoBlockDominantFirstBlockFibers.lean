import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockQuotient

/-! # Actual product fibers in the first-block disintegration -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory ProbabilityTheory GeneralLinear Whittaker HarmonicAnalysis QuotientIntegration
  TwoBlockJacquet TwoBlockUnipotentQuotient
open scoped ENNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance firstFiberTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance firstFiberValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance firstFiberLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance firstFiberT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance firstFiberCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance firstFiberGLTopology (a : ℕ) :
    IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a
local instance firstFiberGLLocalCompact (a : ℕ) :
    LocallyCompactSpace (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace a
local instance firstFiberGLCountable (a : ℕ) :
    SecondCountableTopology (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology a
local instance firstFiberMeasurable : MeasurableSpace F.Carrier := borel _
local instance firstFiberBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance firstFiberGLMeasurable (a : ℕ) :
    MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance firstFiberGLBorel (a : ℕ) :
    BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance firstFiberNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F.Carrier) := borel _
local instance firstFiberNBorel (a : ℕ) :
    BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
local instance firstFiberNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance firstFiberNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance firstFiberNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
  {ψ : UnitaryAdditiveCharacter F.Carrier}

local instance firstFiberHMeasurable :
    MeasurableSpace (blockUnipotent h F.Carrier) := borel _
local instance firstFiberHBorel :
    BorelSpace (blockUnipotent h F.Carrier) := ⟨rfl⟩
local instance firstFiberHQMeasurable :
    MeasurableSpace (BlockQuotient h F.Carrier) := borel _
local instance firstFiberHQBorel :
    BorelSpace (BlockQuotient h F.Carrier) := ⟨rfl⟩

local instance firstFiberMixedSubgroupMeasurable :
    MeasurableSpace (TwoBlockFirstBlockQuotient.mixedSubgroup F h) := borel _
local instance firstFiberMixedSubgroupBorel :
    BorelSpace (TwoBlockFirstBlockQuotient.mixedSubgroup F h) := ⟨rfl⟩
local instance firstFiberMixedMeasurable :
    MeasurableSpace (TwoBlockFirstBlockQuotient.MixedQuotient F h) := borel _
local instance firstFiberMixedBorel :
    BorelSpace (TwoBlockFirstBlockQuotient.MixedQuotient F h) := ⟨rfl⟩

variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (f : Sections F h σ)

/-- The real integral of the raw rectangle norm on the block quotient. -/
def rectangularSectionNormProfile (j k : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (ν : AdditiveHaarMeasure F.Carrier)
    (weight : LeftUnipotentQuotient t F.Carrier → ℂ)
    (z : BlockQuotient h F.Carrier) : ℝ :=
  ∫ x, ‖rectangularSectionIntegrand F ell f j k Wtest weight x z‖
    ∂rectangularMeasure ν j (t + 1)

/-- Disintegrate the real raw-norm profile before invoking Fubini on the
actual first-block quotient times the actual external rectangle. -/
theorem rectangularSection_firstBlock_product_fibers (j k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (weight : LeftUnipotentQuotient t F.Carrier → ℂ) (hw : Continuous weight)
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    [μR.IsAddHaarMeasure] (hraw : IsAbsIntegrable ψ (fun i => (ell i).val) μR f)
    (ν : AdditiveHaarMeasure F.Carrier)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (νH : Measure (BlockQuotient h F.Carrier)) [SigmaFinite νH]
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SigmaFinite νA]
    (νM : Measure (TwoBlockFirstBlockQuotient.MixedQuotient F h))
    (hνN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN)
    (hνH : IsCompatible (blockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (blockHaar F.Carrier h) νH)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (hνM : IsCompatible (TwoBlockFirstBlockQuotient.mixedSubgroup F h)
      (generalLinearHaar F.Carrier t) (TwoBlockFirstBlockQuotient.mixedHaar F h) νM)
    (a : ℤ) :
    let hInv := TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible F (m 0)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA hνA
    let κ := TwoBlockFirstBlockQuotient.fiberKernel F h νA hInv a
    let N := rectangularSectionNormProfile F ell f j k Wtest.val ν weight
    let P := fun q => ∫ z, N z ∂κ q
    let μM := νM.restrict (TwoBlockFirstBlockQuotient.determinantSlice F h 0)
    Measurable N ∧
    Integrable N (νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h a)) ∧
    Measurable P ∧ Integrable P μM ∧
    (∀ q (g : GeneralLinear (t + 1) F.Carrier), q = Quotient.mk _ g →
      P q = ∫ v in RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) a,
        ∫ x, ‖rectangularSectionIntegrand F ell f j k Wtest.val weight x
          (TwoBlockFirstBlockQuotient.fiberPoint h F.Carrier v g)‖
          ∂rectangularMeasure ν j (t + 1) ∂νA) ∧
    ∀ᵐ q ∂μM, ∀ g : GeneralLinear (t + 1) F.Carrier, q = Quotient.mk _ g →
      Integrable (fun z : LeftUnipotentQuotient (m 0) F.Carrier ×
          Matrix (Fin j) (Fin (t + 1)) F.Carrier =>
        rectangularSectionIntegrand F ell f j k Wtest.val weight z.2
          (TwoBlockFirstBlockQuotient.fiberPoint h F.Carrier z.1 g))
        ((νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData
          (m 0) a)).prod (rectangularMeasure ν j (t + 1))) ∧
      TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInv a
        (rectangularSectionAverage F ell f j k Wtest.val ν weight) q =
        ∫ x, ∫ v in RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) a,
          rectangularSectionIntegrand F ell f j k Wtest.val weight x
            (TwoBlockFirstBlockQuotient.fiberPoint h F.Carrier v g) ∂νA
              ∂rectangularMeasure ν j (t + 1) := by
  dsimp only
  let hInv := TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible F (m 0)
    (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA hνA
  let κ := TwoBlockFirstBlockQuotient.fiberKernel F h νA hInv a
  let μM := νM.restrict (TwoBlockFirstBlockQuotient.determinantSlice F h 0)
  let μA := νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) a)
  let E := fun z : BlockQuotient h F.Carrier ×
      Matrix (Fin j) (Fin (t + 1)) F.Carrier =>
    rectangularSectionIntegrand F ell f j k Wtest.val weight z.2 z.1
  let N := rectangularSectionNormProfile F ell f j k Wtest.val ν weight
  have hreg := rectangularSectionIntegrand_regular F ell f j k π hπ lambda Wtest ν weight hw
  have hEi := rectangularSectionIntegrand_integrable F ell f j k π hπ lambda Wtest
    weight hw μR hraw ν νN νH hνN hνH a
  have hNm : Measurable N := hreg.1.measurable.stronglyMeasurable.norm.integral_prod_right'.measurable
  have hNi : Integrable N
      (νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h a)) :=
    hEi.integral_norm_prod_left
  have hNnonneg (z : BlockQuotient h F.Carrier) : 0 ≤ N z :=
    integral_nonneg fun _ => norm_nonneg _
  have hzero := (TwoBlockFirstBlockQuotient.normalized_tower F h
    νA hInv hνA νM hνM νH hνH).2
  have hcomp := TwoBlockFirstBlockQuotient.fiberKernel_comp_zeroSlice_eq F h
    νA hInv hνA νM hνM νH hzero a
  have hNc : Integrable N (κ ∘ₘ μM) := by rw [hcomp]; exact hNi
  obtain ⟨hNae, hPi⟩ := (Measure.integrable_comp_iff hNm.aestronglyMeasurable).mp hNc
  have hPnorm : (fun q => ∫ z, ‖N z‖ ∂κ q) = fun q => ∫ z, N z ∂κ q := by
    funext q
    simp only [Real.norm_eq_abs, abs_of_nonneg (hNnonneg _)]
  rw [hPnorm] at hPi
  refine ⟨hNm, hNi, (hNm.stronglyMeasurable.integral_kernel (κ := κ)).measurable,
    hPi, ?_, ?_⟩
  · intro q g hq
    subst q
    rw [TwoBlockFirstBlockQuotient.fiberKernel_mk]
    have hfm : Measurable (fun v : LeftUnipotentQuotient (m 0) F.Carrier =>
        TwoBlockFirstBlockQuotient.fiberPoint h F.Carrier v g) :=
      ((TwoBlockFirstBlockQuotient.continuous_fiberPoint F h).comp
        (continuous_id.prodMk continuous_const)).measurable
    exact integral_map hfm.aemeasurable hNm.aestronglyMeasurable
  · filter_upwards [hNae] with q hq g hqg
    subst q
    have hfm : Measurable (fun v : LeftUnipotentQuotient (m 0) F.Carrier =>
        TwoBlockFirstBlockQuotient.fiberPoint h F.Carrier v g) :=
      ((TwoBlockFirstBlockQuotient.continuous_fiberPoint F h).comp
        (continuous_id.prodMk continuous_const)).measurable
    rw [TwoBlockFirstBlockQuotient.fiberKernel_mk] at hq
    have hNactual := hq.comp_measurable hfm
    have hEm : StronglyMeasurable (fun z : LeftUnipotentQuotient (m 0) F.Carrier ×
        Matrix (Fin j) (Fin (t + 1)) F.Carrier =>
        E (TwoBlockFirstBlockQuotient.fiberPoint h F.Carrier z.1 g, z.2)) :=
      hreg.1.measurable.stronglyMeasurable.comp_measurable
        ((hfm.comp measurable_fst).prodMk measurable_snd)
    have hactual : Integrable (fun z : LeftUnipotentQuotient (m 0) F.Carrier ×
        Matrix (Fin j) (Fin (t + 1)) F.Carrier =>
        E (TwoBlockFirstBlockQuotient.fiberPoint h F.Carrier z.1 g, z.2))
        (μA.prod (rectangularMeasure ν j (t + 1))) := by
      apply (integrable_prod_iff hEm.aestronglyMeasurable).mpr
      constructor
      · exact Filter.Eventually.of_forall fun v =>
          hreg.2.1 (TwoBlockFirstBlockQuotient.fiberPoint h F.Carrier v g)
      · exact hNactual
    refine ⟨hactual, ?_⟩
    rw [TwoBlockFirstBlockQuotient.firstBlockAverage_mk]
    exact integral_integral_swap hactual

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
