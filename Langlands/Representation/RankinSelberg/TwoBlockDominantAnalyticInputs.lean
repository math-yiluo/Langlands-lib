import Langlands.Representation.RankinSelberg.TwoBlockDominantSliceConvergence
import Langlands.Representation.RankinSelberg.TwoBlockDominantUpperSliceAnalysis
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasurePackage

/-! # Uniform analytic inputs for the dominant first-block identity -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  TwoBlockLowerUnipotentQuotient TwoBlockDominantRectangular

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance analyticInputsTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance analyticInputsValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance analyticInputsLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance analyticInputsT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance analyticInputsSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance analyticInputsGLGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n
local instance analyticInputsGLCompact (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance analyticInputsGLSecondCountable (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance analyticInputsMeasurable : MeasurableSpace F.Carrier := borel _
local instance analyticInputsBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance analyticInputsGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance analyticInputsGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance analyticInputsNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance analyticInputsNBorel (n : ℕ) :
    BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance analyticInputsQMeasurable (t : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient t F.Carrier) := borel _
local instance analyticInputsQBorel (t : ℕ) :
    BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
local instance analyticInputsLowerMeasurable {t : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i + 1) = t + 1) :
    MeasurableSpace (LowerQuotient h F.Carrier) := borel _
local instance analyticInputsLowerBorel {t : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i + 1) = t + 1) :
    BorelSpace (LowerQuotient h F.Carrier) := ⟨rfl⟩

/-- Existence of both exact standard quotient measures is independent of the
sections, representations and additive Haar measure. -/
theorem compatible_standard_quotients (t a : ℕ) :
    ∃ (hN : Measure.IsMulRightInvariant (unipotentHaar F.Carrier t))
      (hNA : Measure.IsMulRightInvariant (unipotentHaar F.Carrier a)),
      letI := hN
      letI := hNA
      (∃ νN : Measure (LeftUnipotentQuotient t F.Carrier),
        IsCompatible (upperUnipotent (t + 1) F.Carrier)
          (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN) ∧
      (∃ νA : Measure (LeftUnipotentQuotient a F.Carrier),
        IsCompatible (upperUnipotent (a + 1) F.Carrier)
          (generalLinearHaar F.Carrier a) (unipotentHaar F.Carrier a) νA) := by
  refine ⟨unipotentHaar_isMulRightInvariant F.Carrier t,
    unipotentHaar_isMulRightInvariant F.Carrier a, ?_⟩
  exact ⟨unipotent_compatibleMeasureExists F.Carrier t,
    unipotent_compatibleMeasureExists F.Carrier a⟩

variable {t r : ℕ} {m : Fin 2 → ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- All analytic clauses of the first-block target, with one bound and one
ordinary Jacquet functional before every supplied measure and test. -/
def HasUniformAnalyticInputs
    (h : ∑ i, (m i + 1) = t + 1) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) (C : ℝ) : Prop :=
  ∀ u : ℝ, C < u →
    let σu := twoBlockOppositeTwistBlocks F m τ u
    let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
    let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
    (∀ f : TwoBlockJacquet.Sections F h σu,
      TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ellu i).val) μR f) ∧
    ∃ J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σu),
      ((∀ i, (ell i).val ≠ 0) → J.val ≠ 0) ∧
      (∀ (f : TwoBlockJacquet.Sections F h σu)
        (g : GeneralLinear (t + 1) F.Carrier),
        J.val (TwoBlockJacquet.inducedRep F h σu g f) =
          TwoBlockJacquet.jacquetFunction ψ (fun i => (ellu i).val) μR f g) ∧
      ∀ (hN : Measure.IsMulRightInvariant (unipotentHaar F.Carrier t))
        (hNA : Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 0))),
        letI := hN
        letI := hNA
        ∀ (νN : Measure (LeftUnipotentQuotient t F.Carrier))
          (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)),
          IsCompatible (upperUnipotent (t + 1) F.Carrier)
            (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN →
          IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
            (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA →
          let νMinus : Measure (LowerQuotient h F.Carrier) :=
            Measure.map (lowerToStandard h F.Carrier).symm νN
          SigmaFinite νN ∧ SigmaFinite νA ∧ SigmaFinite νMinus ∧
          ∀ (j k : ℕ) (hr : r = t + (j + k + 1))
            (f : TwoBlockJacquet.Sections F h σu)
            (Wtest : (coefficientModel π lambda).toSubmodule),
            let Wup : WhittakerFunctions ψ (t + (j + k + 1)) := hr ▸ Wtest.val
            let Wjac := (modelMap (TwoBlockJacquet.inducedRep F h σu) J f).val
            let μrect := rectangularMeasure ν.val j (t + 1)
            let A := unequalRankAverage F j k ψ
              (rectangularBorelMeasure F ν.val j (t + 1)) Wup Wjac 0
            let K := quotientKernel ν.val ellu f Wtest.val hr 0
            let Nprofile := quotientNormProfile ν.val ellu f Wtest.val hr 0
            let Fiber := quotientFiberIntegrable ν.val ellu f Wtest.val hr 0
            Measurable A ∧ Measurable K ∧
            ∀ a : ℤ,
              Integrable (fun z : LeftUnipotentQuotient t F.Carrier ×
                Matrix (Fin j) (Fin (t + 1)) F.Carrier =>
                  unequalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
                    j k Wup Wjac 0 z.2 z.1)
                ((νN.restrict (RankinSelberg.determinantSlice
                  F.canonicalTopologicalData t a)).prod μrect) ∧
              Integrable K (νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h a)) ∧
              Integrable Nprofile (νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h a)) ∧
              ∀ᵐ z ∂νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h a), Fiber z

/-- The maximum of the ordinary Jacquet and raw-norm thresholds proves every
analytic clause without a small-block epsilon premise. -/
theorem exists_uniform_analytic_inputs
    (h : ∑ i, (m i + 1) = t + 1) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) :
    ∃ C : ℝ, HasUniformAnalyticInputs F h ψ ν π lambda τ ell C := by
  obtain ⟨CJ, hCJ⟩ := exists_uniformOrdinaryJacquetRealization F h ψ ν τ hτ ell
  obtain ⟨CL, hCL⟩ :=
    exists_uniform_slice_convergence ν.val h ψ π hπ lambda τ hτ ell
  refine ⟨max CJ CL, fun u hu => ?_⟩
  obtain ⟨habs, J, hJ0, hJ⟩ := hCJ u ((le_max_left CJ CL).trans_lt hu)
  refine ⟨habs, J, hJ0, hJ, ?_⟩
  intro hN hNA
  let := hN
  let := hNA
  intro νN νA hνN hνA
  have hsf := standardCompatible_sigmaFinite F h hN νN hνN
  have hsfA := TwoBlockLowerFirstBlockQuotient.compatibleQuotient_sigmaFinite
    F (m 0) (upperUnipotent (m 0 + 1) F.Carrier)
      (UpperUnipotent.isClosed (R := F.Carrier)) _ νA hνA
  refine ⟨hsf.1, hsfA, hsf.2, ?_⟩
  intro j k hr f Wtest
  subst r
  dsimp only
  let σu := twoBlockOppositeTwistBlocks F m τ u
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
  have hσ : IsOfWhittakerType t (inverseStandardCharacter ψ t)
      (TwoBlockJacquet.inducedRep F h σu) :=
    DominantRankTransport.lowerInduced_inverseWhittakerType F h ψ σu
      (fun i => (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff
        F m τ u i _).mpr (hτ i))
  obtain ⟨hm, _, hi⟩ :=
    hCL u ((le_max_right CJ CL).trans_lt hu) hN νN hνN f j k rfl Wtest
  refine ⟨(continuous_upperAverage F j k ψ π (TwoBlockJacquet.inducedRep F h σu)
      lambda J Wtest (modelMap (TwoBlockJacquet.inducedRep F h σu) J f)
      hπ hσ.1.1 ν.val 0).measurable, (hm 0).1, fun a => ?_⟩
  refine ⟨upperSliceConverges F j k ψ π (TwoBlockJacquet.inducedRep F h σu)
    lambda J Wtest (modelMap (TwoBlockJacquet.inducedRep F h σu) J f)
    hπ hσ νN hνN ν.val a, ?_⟩
  have hli := hi 0 a
  change Integrable _ _ ∧ Integrable _ _ ∧ _ at hli
  have hμ : TwoBlockLowerFixedSlice.lowerMeasure F h
      (νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t a)) =
      (TwoBlockLowerFixedSlice.lowerMeasure F h νN).restrict
        (TwoBlockLowerUnipotentQuotient.determinantSlice F h a) :=
    (TwoBlockLowerFixedSlice.lowerMeasure_restrict F h νN a).symm
  rw [hμ] at hli
  exact hli

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
