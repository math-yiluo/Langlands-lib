import Langlands.Representation.RankinSelberg.TwoBlockDominantDiagonalSupport
import Langlands.Representation.RankinSelberg.TwoBlockFixedSliceAnalysis
import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationProof
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Section unfolding with compact diagonal norm support -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis QuotientIntegration
  TwoBlockJacquet TwoBlockUnipotentQuotient
open scoped ENNReal

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance sectionUnfoldingTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance sectionUnfoldingValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance sectionUnfoldingLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance sectionUnfoldingT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance sectionUnfoldingCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance sectionUnfoldingGLTopology (a : ℕ) :
    IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a
local instance sectionUnfoldingGLLocalCompact (a : ℕ) :
    LocallyCompactSpace (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace a
local instance sectionUnfoldingGLCountable (a : ℕ) :
    SecondCountableTopology (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology a
local instance sectionUnfoldingMeasurable : MeasurableSpace F.Carrier := borel _
local instance sectionUnfoldingBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance sectionUnfoldingGLMeasurable (a : ℕ) :
    MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance sectionUnfoldingGLBorel (a : ℕ) :
    BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance sectionUnfoldingNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F.Carrier) := borel _
local instance sectionUnfoldingNBorel (a : ℕ) :
    BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
local instance sectionUnfoldingNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance sectionUnfoldingNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance sectionUnfoldingNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
  {ψ : UnitaryAdditiveCharacter F.Carrier}

local instance sectionUnfoldingHMeasurable :
    MeasurableSpace (blockUnipotent h F.Carrier) := borel _
local instance sectionUnfoldingHBorel :
    BorelSpace (blockUnipotent h F.Carrier) := ⟨rfl⟩
local instance sectionUnfoldingHQMeasurable :
    MeasurableSpace (BlockQuotient h F.Carrier) := borel _
local instance sectionUnfoldingHQBorel :
    BorelSpace (BlockQuotient h F.Carrier) := ⟨rfl⟩

variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (f : Sections F h σ) (Wtest : WhittakerFunctions ψ t)
  (weight : LeftUnipotentQuotient t F.Carrier → ℂ)

private theorem sectionProduct_invariant (v : blockUnipotent h F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    Wtest.val (v.val * g) * scalarSection (fun i => (ell i).val) f (v.val * g) 1 =
      Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 := by
  obtain ⟨_, n, rfl⟩ := v
  let u : upperUnipotent (t + 1) F.Carrier :=
    ⟨blockEmbedding h F.Carrier n, blockEmbedding_mem_upperUnipotent h F.Carrier n⟩
  rw [Wtest.property u,
    TwoBlockUnfolding.scalarSection_blockEmbedding_mul_eq_inverseStandardCharacter ell f n g]
  have hc : (standardCharacter ψ t u : ℂ) * (inverseStandardCharacter ψ t u : ℂ) = 1 :=
    Units.mul_inv (standardCharacter ψ t u)
  calc
    _ = ((standardCharacter ψ t u : ℂ) * (inverseStandardCharacter ψ t u : ℂ)) *
        (Wtest.val g * scalarSection (fun i => (ell i).val) f g 1) := by ring
    _ = _ := by rw [hc, one_mul]

/-- The actual diagonal test times the scalar section, descended to the block
unipotent quotient and multiplied by a scalar function on the standard quotient. -/
def sectionIntegrand (z : BlockQuotient h F.Carrier) : ℂ :=
  descend (blockUnipotent h F.Carrier)
    (fun g => Wtest.val g * scalarSection (fun i => (ell i).val) f g 1)
    (sectionProduct_invariant F ell f Wtest) z *
      weight (projection h F.Carrier z)

@[simp] theorem sectionIntegrand_mk (g : GeneralLinear (t + 1) F.Carrier) :
    sectionIntegrand F ell f Wtest weight (Quotient.mk _ g) =
      Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 *
        weight (Quotient.mk _ g) := rfl

/-- The raw ordinary Jacquet integrand is the exact fiber function. -/
theorem sectionIntegrand_fiberPoint
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    sectionIntegrand F ell f Wtest weight (fiberPoint h F.Carrier x g) =
      Wtest.val g * TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g x *
        weight (Quotient.mk _ g) := by
  have hproj := projection_fiberPoint h F.Carrier x g
  let v : upperUnipotent (t + 1) F.Carrier :=
    ⟨upperRadical h F.Carrier x, upperRadical_mem_upperUnipotent h F.Carrier x⟩
  have hW : Wtest.val (upperRadical h F.Carrier x * g) =
      positiveKernel ψ x * Wtest.val g := by
    rw [positiveKernel_eq_superdiagonal_upperRadical ψ h x]
    exact Wtest.property v g
  change _ * weight (projection h F.Carrier (fiberPoint h F.Carrier x g)) = _
  rw [hproj]
  change Wtest.val (upperRadical h F.Carrier x * g) *
    scalarSection (fun i => (ell i).val) f (upperRadical h F.Carrier x * g) 1 * _ = _
  rw [hW, TwoBlockJacquet.integrand_def]
  ring

theorem sectionIntegrand_continuous (hW : Continuous Wtest.val)
    (hw : Continuous weight) : Continuous (sectionIntegrand F ell f Wtest weight) := by
  have hs : Continuous (fun g => scalarSection (fun i => (ell i).val) f g 1) := by
    simpa only [scalarSection_one, Function.comp_def] using
      ((Induction.eval_isLocallyConstant _ _ f).comp
        (tensorContraction (fun i => (ell i).val))).continuous
  have hbase : Continuous (descend (blockUnipotent h F.Carrier)
      (fun g => Wtest.val g * scalarSection (fun i => (ell i).val) f g 1)
      (sectionProduct_invariant F ell f Wtest)) := by
    apply (leftQuotient_isOpenQuotientMap (blockUnipotent h F.Carrier)).isQuotientMap.continuous_iff.mpr
    exact hW.mul hs
  exact hbase.mul (hw.comp (continuous_projection F h))

variable (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
  [μR.IsAddHaarMeasure]

/-- The signed fiber average uses the supplied ordinary Jacquet integral. -/
theorem sectionAverage_mk (g : GeneralLinear (t + 1) F.Carrier) :
    radicalAverage F h μR (sectionIntegrand F ell f Wtest weight) (Quotient.mk _ g) =
      Wtest.val g * jacquetFunction ψ (fun i => (ell i).val) μR f g *
        weight (Quotient.mk _ g) := by
  simp only [radicalAverage_mk, sectionIntegrand_fiberPoint, jacquetFunction_def,
    integral_mul_const, integral_const_mul]

/-- The absolute fiber average retains the integral of the raw norm. -/
theorem sectionNormAverage_mk (g : GeneralLinear (t + 1) F.Carrier) :
    radicalAverage F h μR (fun z => (‖sectionIntegrand F ell f Wtest weight z‖ : ℂ))
      (Quotient.mk _ g) =
      (‖Wtest.val g‖ : ℂ) *
        (∫ x, (‖TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g x‖ : ℂ) ∂μR) *
        (‖weight (Quotient.mk _ g)‖ : ℂ) := by
  simp only [radicalAverage_mk, sectionIntegrand_fiberPoint, norm_mul,
    Complex.ofReal_mul, integral_mul_const, integral_const_mul]

theorem sectionAverages_continuous (hW : Continuous Wtest.val) (hw : Continuous weight) :
    Continuous (radicalAverage F h μR (sectionIntegrand F ell f Wtest weight)) ∧
    Continuous (radicalAverage F h μR
      (fun z => (‖sectionIntegrand F ell f Wtest weight z‖ : ℂ))) := by
  have hlc := TwoBlockUnfolding.rawIntegrand_isLocallyConstant ψ (fun i => (ell i).val) f
  have hj : Continuous (jacquetFunction ψ (fun i => (ell i).val) μR f) :=
    (hlc.comp (fun v => ∫ x, v x ∂μR)).continuous
  have ha : Continuous (fun g => ∫ x,
      (‖TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g x‖ : ℂ) ∂μR) :=
    (hlc.comp (fun v => ∫ x, (‖v x‖ : ℂ) ∂μR)).continuous
  have hwg := hw.comp (continuous_quotient_mk' :
    Continuous (fun g : GeneralLinear (t + 1) F.Carrier =>
      (Quotient.mk _ g : LeftUnipotentQuotient t F.Carrier)))
  constructor
  · apply (leftQuotient_isOpenQuotientMap (upperUnipotent (t + 1) F.Carrier)).isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, sectionAverage_mk, leftQuotientMap_apply,
      Pi.mul_def, Quotient.mk'] using
      (hW.mul hj).mul hwg
  · apply (leftQuotient_isOpenQuotientMap (upperUnipotent (t + 1) F.Carrier)).isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, sectionNormAverage_mk, leftQuotientMap_apply,
      Pi.mul_def, Quotient.mk'] using
      ((Complex.continuous_ofReal.comp hW.norm).mul ha).mul
        (Complex.continuous_ofReal.comp hwg.norm)

/-- Compact norm support on the fixed slice and ordinary raw Jacquet convergence
give absolute block-quotient convergence and the normalized first unfolding. -/
theorem sectionIntegrand_slice_unfolding (hW : Continuous Wtest.val)
    (hw : Continuous weight) (hraw : IsAbsIntegrable ψ (fun i => (ell i).val) μR f)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (νH : Measure (BlockQuotient h F.Carrier))
    (hνN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN)
    (hνH : IsCompatible (blockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (blockHaar F.Carrier h) νH)
    (a : ℤ)
    (hcompact : HasCompactSupport
      ((RankinSelberg.determinantSlice F.canonicalTopologicalData t a).indicator
        (whittakerNorm ψ Wtest))) :
    let slice := RankinSelberg.determinantSlice F.canonicalTopologicalData t a
    let E := sectionIntegrand F ell f Wtest weight
    let c := μR {x | ∀ i j, x i j ∈ (ValuativeRel.valuation F.Carrier).integer}
    Integrable E (νH.restrict (projection h F.Carrier ⁻¹' slice)) ∧
    Integrable (radicalAverage F h μR (fun z => (‖E z‖ : ℂ))) (νN.restrict slice) ∧
    Integrable (radicalAverage F h μR E) (νN.restrict slice) ∧
    (∫ q, radicalAverage F h μR E q ∂νN.restrict slice) =
      c.toReal • (∫ z, E z ∂νH.restrict (projection h F.Carrier ⁻¹' slice)) := by
  dsimp only
  let E := sectionIntegrand F ell f Wtest weight
  let slice := RankinSelberg.determinantSlice F.canonicalTopologicalData t a
  let Aabs := radicalAverage F h μR (fun z => (‖E z‖ : ℂ))
  have hEc := sectionIntegrand_continuous F ell f Wtest weight hW hw
  obtain ⟨_, hAabsc⟩ := sectionAverages_continuous F ell f Wtest weight μR hW hw
  let := hνN.regular
  let := leftQuotient_locallyCompactSpace (upperUnipotent (t + 1) F.Carrier)
  let := Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap (upperUnipotent (t + 1) F.Carrier))
  have hslice : IsClopen slice := RankinSelberg.isClopen_determinantSlice _ t a
  have habs_zero : ∀ q, whittakerNorm ψ Wtest q = 0 → Aabs q = 0 := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      intro hz
      rw [whittakerNorm_mk] at hz
      change radicalAverage F h μR (fun z => (‖sectionIntegrand F ell f Wtest weight z‖ : ℂ))
        (Quotient.mk _ g) = 0
      rw [sectionNormAverage_mk, hz, Complex.ofReal_zero, zero_mul, zero_mul]
  have hsupport : HasCompactSupport (slice.indicator Aabs) := by
    apply hcompact.mono
    intro q hq hz
    change slice.indicator Aabs q ≠ 0 at hq
    change slice.indicator (whittakerNorm ψ Wtest) q = 0 at hz
    by_cases hqs : q ∈ slice
    · rw [Set.indicator_of_mem hqs] at hq hz
      exact hq (habs_zero q hz)
    · simp only [Set.indicator_of_notMem hqs] at hq
      exact hq rfl
  have hAabsi : Integrable Aabs (νN.restrict slice) := by
    apply (integrable_indicator_iff hslice.isOpen.measurableSet).mp
    exact (hslice.continuous_indicator hAabsc).integrable_of_hasCompactSupport hsupport
  obtain ⟨_, _, _, _, _, _, htower⟩ := twoBlockUnipotentQuotientIntegration p F t m h
  obtain ⟨_, _, κ, hκfin, hκ, htowerR⟩ := htower μR
  let := hκfin
  have hfiber : ∀ g : GeneralLinear (t + 1) F.Carrier,
      Integrable (fun x => E (fiberPoint h F.Carrier x g)) μR := by
    intro g
    simpa only [E, sectionIntegrand_fiberPoint] using
      ((hraw g).const_mul (Wtest.val g)).mul_const (weight (Quotient.mk _ g))
  have hκfiber : ∀ q, Integrable E (κ q) := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [hκ g]
      have hcont : Continuous (fun x => fiberPoint h F.Carrier x g) :=
        continuous_quotient_mk'.comp
          ((TwoBlockJacquet.continuous_upperRadical h F.Carrier).mul continuous_const)
      exact (integrable_map_measure hEc.aestronglyMeasurable
        hcont.measurable.aemeasurable).mpr (hfiber g)
  have habs_eq : Aabs = fun q => Complex.ofReal (∫ z, ‖E z‖ ∂κ q) := by
    simpa only [integral_complex_ofReal] using
      radicalAverage_eq_integral_kernel F h μR κ hκ
        (fun z => (‖E z‖ : ℂ)) (Complex.measurable_ofReal.comp hEc.measurable.norm)
  have hnorm : Integrable (fun q => ∫ z, ‖E z‖ ∂κ q) (νN.restrict slice) := by
    have hr := hAabsi.re
    change Integrable (fun q => (Aabs q).re) (νN.restrict slice) at hr
    rw [habs_eq] at hr
    exact hr
  obtain ⟨_, _, ht⟩ := htowerR νN νH hνN hνH
  have htE := (ht slice hslice.isOpen.measurableSet).2.2 E hEc.measurable
  have hEi := htE.1.mpr ⟨Filter.Eventually.of_forall hκfiber, hnorm⟩
  obtain ⟨hAi, hidentity⟩ := htE.2 hEi
  exact ⟨hEi, hAabsi, hAi, hidentity⟩

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
