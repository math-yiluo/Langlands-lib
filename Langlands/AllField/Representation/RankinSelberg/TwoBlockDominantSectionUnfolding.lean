import Langlands.Representation.RankinSelberg.TwoBlockDominantSectionUnfolding
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantDiagonalSupport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFixedSliceAnalysis
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationProof
/-! # Section unfolding with compact diagonal norm support -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding diagonalSupportGLTopological diagonalSupportT2 diagonalSupportTopology diagonalWhittaker_slice_hasCompactSupport sectionAverage_mk sectionAverages_continuous sectionIntegrand sectionIntegrand_continuous sectionIntegrand_fiberPoint sectionIntegrand_mk sectionIntegrand_slice_unfolding sectionNormAverage_mk sectionUnfoldingBorel sectionUnfoldingCountable sectionUnfoldingGLBorel sectionUnfoldingGLCountable sectionUnfoldingGLLocalCompact sectionUnfoldingGLMeasurable sectionUnfoldingGLTopology sectionUnfoldingHBorel sectionUnfoldingHMeasurable sectionUnfoldingHQBorel sectionUnfoldingHQMeasurable sectionUnfoldingLocalField sectionUnfoldingMeasurable sectionUnfoldingNBorel sectionUnfoldingNCountable sectionUnfoldingNMeasurable sectionUnfoldingNQBorel sectionUnfoldingNQMeasurable sectionUnfoldingT2 sectionUnfoldingTopology sectionUnfoldingValuation
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockUnipotentQuotientIntegrationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockUnipotentQuotientIntegration whittakerRowSliceCompactSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding FiberKernelSFiniteStatement analytic_of_comp_eq_smul continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul fiberKernel fiberKernel_compact_ne_top fiberKernel_isSFinite fiberKernel_mk fiberMeasures_upperUnipotent_mul iUnion_determinantSlice integerCube_mass_pos_lt_top isClopen_determinantSlice map_unipotentShift measurableSet_determinantSlice measurable_fiberMeasures mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice radicalAverage radicalAverage_eq_integral_kernel radicalAverage_mk
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient hiding determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open scoped ENNReal

universe uF uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance sectionUnfoldingT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance sectionUnfoldingCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance sectionUnfoldingGLTopology (a : ℕ) :
    IsTopologicalGroup (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup a
local instance sectionUnfoldingGLLocalCompact (a : ℕ) :
    LocallyCompactSpace (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace a
local instance sectionUnfoldingGLCountable (a : ℕ) :
    SecondCountableTopology (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology a
local instance sectionUnfoldingMeasurable : MeasurableSpace F := borel _
local instance sectionUnfoldingBorel : BorelSpace F := ⟨rfl⟩
local instance sectionUnfoldingGLMeasurable (a : ℕ) :
    MeasurableSpace (GeneralLinear a F) := borel _
local instance sectionUnfoldingGLBorel (a : ℕ) :
    BorelSpace (GeneralLinear a F) := ⟨rfl⟩
local instance sectionUnfoldingNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F) := borel _
local instance sectionUnfoldingNBorel (a : ℕ) :
    BorelSpace (upperUnipotent a F) := ⟨rfl⟩
local instance sectionUnfoldingNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance sectionUnfoldingNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F) := borel _
local instance sectionUnfoldingNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
  {ψ : UnitaryAdditiveCharacter F}

local instance sectionUnfoldingHMeasurable :
    MeasurableSpace (blockUnipotent h F) := borel _
local instance sectionUnfoldingHBorel :
    BorelSpace (blockUnipotent h F) := ⟨rfl⟩
local instance sectionUnfoldingHQMeasurable :
    MeasurableSpace (BlockQuotient h F) := borel _
local instance sectionUnfoldingHQBorel :
    BorelSpace (BlockQuotient h F) := ⟨rfl⟩

variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (f : Sections F h σ) (Wtest : WhittakerFunctions ψ t)
  (weight : LeftUnipotentQuotient t F → ℂ)

private theorem sectionProduct_invariant (v : blockUnipotent h F)
    (g : GeneralLinear (t + 1) F) :
    Wtest.val (v.val * g) * scalarSection (fun i => (ell i).val) f (v.val * g) 1 =
      Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 := by
  obtain ⟨_, n, rfl⟩ := v
  let u : upperUnipotent (t + 1) F :=
    ⟨blockEmbedding h F n, blockEmbedding_mem_upperUnipotent h F n⟩
  rw [Wtest.property u,
    Langlands.AllField.RankinSelberg.TwoBlockUnfolding.scalarSection_blockEmbedding_mul_eq_inverseStandardCharacter ell f n g]
  have hc : (standardCharacter ψ t u : ℂ) * (inverseStandardCharacter ψ t u : ℂ) = 1 :=
    Units.mul_inv (standardCharacter ψ t u)
  calc
    _ = ((standardCharacter ψ t u : ℂ) * (inverseStandardCharacter ψ t u : ℂ)) *
        (Wtest.val g * scalarSection (fun i => (ell i).val) f g 1) := by ring
    _ = _ := by rw [hc, one_mul]

/-- The actual diagonal test times the scalar section, descended to the block
unipotent quotient and multiplied by a scalar function on the standard quotient. -/
def sectionIntegrand (z : BlockQuotient h F) : ℂ :=
  descend (blockUnipotent h F)
    (fun g => Wtest.val g * scalarSection (fun i => (ell i).val) f g 1)
    (sectionProduct_invariant F ell f Wtest) z *
      weight (projection h F z)

@[simp] theorem sectionIntegrand_mk (g : GeneralLinear (t + 1) F) :
    sectionIntegrand F ell f Wtest weight (Quotient.mk _ g) =
      Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 *
        weight (Quotient.mk _ g) := rfl

/-- The raw ordinary Jacquet integrand is the exact fiber function. -/
theorem sectionIntegrand_fiberPoint
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F) :
    sectionIntegrand F ell f Wtest weight (fiberPoint h F x g) =
      Wtest.val g * Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g x *
        weight (Quotient.mk _ g) := by
  have hproj := projection_fiberPoint h F x g
  let v : upperUnipotent (t + 1) F :=
    ⟨upperRadical h F x, upperRadical_mem_upperUnipotent h F x⟩
  have hW : Wtest.val (upperRadical h F x * g) =
      positiveKernel ψ x * Wtest.val g := by
    rw [positiveKernel_eq_superdiagonal_upperRadical ψ h x]
    exact Wtest.property v g
  change _ * weight (projection h F (fiberPoint h F x g)) = _
  rw [hproj]
  change Wtest.val (upperRadical h F x * g) *
    scalarSection (fun i => (ell i).val) f (upperRadical h F x * g) 1 * _ = _
  rw [hW, Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand_def]
  ring

theorem sectionIntegrand_continuous (hW : Continuous Wtest.val)
    (hw : Continuous weight) : Continuous (sectionIntegrand F ell f Wtest weight) := by
  have hs : Continuous (fun g => scalarSection (fun i => (ell i).val) f g 1) := by
    simpa only [scalarSection_one, Function.comp_def] using
      ((Induction.eval_isLocallyConstant _ _ f).comp
        (tensorContraction (fun i => (ell i).val))).continuous
  have hbase : Continuous (descend (blockUnipotent h F)
      (fun g => Wtest.val g * scalarSection (fun i => (ell i).val) f g 1)
      (sectionProduct_invariant F ell f Wtest)) := by
    apply (leftQuotient_isOpenQuotientMap (blockUnipotent h F)).isQuotientMap.continuous_iff.mpr
    exact hW.mul hs
  exact hbase.mul (hw.comp (continuous_projection F h))

variable (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
  [μR.IsAddHaarMeasure]

/-- The signed fiber average uses the supplied ordinary Jacquet integral. -/
theorem sectionAverage_mk (g : GeneralLinear (t + 1) F) :
    radicalAverage F h μR (sectionIntegrand F ell f Wtest weight) (Quotient.mk _ g) =
      Wtest.val g * jacquetFunction ψ (fun i => (ell i).val) μR f g *
        weight (Quotient.mk _ g) := by
  simp only [radicalAverage_mk, sectionIntegrand_fiberPoint, jacquetFunction_def,
    integral_mul_const, integral_const_mul]

/-- The absolute fiber average retains the integral of the raw norm. -/
theorem sectionNormAverage_mk (g : GeneralLinear (t + 1) F) :
    radicalAverage F h μR (fun z => (‖sectionIntegrand F ell f Wtest weight z‖ : ℂ))
      (Quotient.mk _ g) =
      (‖Wtest.val g‖ : ℂ) *
        (∫ x, (‖Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g x‖ : ℂ) ∂μR) *
        (‖weight (Quotient.mk _ g)‖ : ℂ) := by
  simp only [radicalAverage_mk, sectionIntegrand_fiberPoint, norm_mul,
    Complex.ofReal_mul, integral_mul_const, integral_const_mul]

theorem sectionAverages_continuous (hW : Continuous Wtest.val) (hw : Continuous weight) :
    Continuous (radicalAverage F h μR (sectionIntegrand F ell f Wtest weight)) ∧
    Continuous (radicalAverage F h μR
      (fun z => (‖sectionIntegrand F ell f Wtest weight z‖ : ℂ))) := by
  have hlc := Langlands.AllField.RankinSelberg.TwoBlockUnfolding.rawIntegrand_isLocallyConstant ψ (fun i => (ell i).val) f
  have hj : Continuous (jacquetFunction ψ (fun i => (ell i).val) μR f) :=
    (hlc.comp (fun v => ∫ x, v x ∂μR)).continuous
  have ha : Continuous (fun g => ∫ x,
      (‖Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g x‖ : ℂ) ∂μR) :=
    (hlc.comp (fun v => ∫ x, (‖v x‖ : ℂ) ∂μR)).continuous
  have hwg := hw.comp (continuous_quotient_mk' :
    Continuous (fun g : GeneralLinear (t + 1) F =>
      (Quotient.mk _ g : LeftUnipotentQuotient t F)))
  constructor
  · apply (leftQuotient_isOpenQuotientMap (upperUnipotent (t + 1) F)).isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, sectionAverage_mk, leftQuotientMap_apply,
      Pi.mul_def, Quotient.mk'] using
      (hW.mul hj).mul hwg
  · apply (leftQuotient_isOpenQuotientMap (upperUnipotent (t + 1) F)).isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, sectionNormAverage_mk, leftQuotientMap_apply,
      Pi.mul_def, Quotient.mk'] using
      ((Complex.continuous_ofReal.comp hW.norm).mul ha).mul
        (Complex.continuous_ofReal.comp hwg.norm)

/-- Compact norm support on the fixed slice and ordinary raw Jacquet convergence
give absolute block-quotient convergence and the normalized first unfolding. -/
theorem sectionIntegrand_slice_unfolding (hW : Continuous Wtest.val)
    (hw : Continuous weight) (hraw : IsAbsIntegrable ψ (fun i => (ell i).val) μR f)
    (νN : Measure (LeftUnipotentQuotient t F))
    (νH : Measure (BlockQuotient h F))
    (hνN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) νN)
    (hνH : IsCompatible (blockUnipotent h F)
      (generalLinearHaar F t) (blockHaar F h) νH)
    (a : ℤ)
    (hcompact : HasCompactSupport
      ((Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t a).indicator
        (whittakerNorm ψ Wtest))) :
    let slice := Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t a
    let E := sectionIntegrand F ell f Wtest weight
    let c := μR {x | ∀ i j, x i j ∈ (ValuativeRel.valuation F).integer}
    Integrable E (νH.restrict (projection h F ⁻¹' slice)) ∧
    Integrable (radicalAverage F h μR (fun z => (‖E z‖ : ℂ))) (νN.restrict slice) ∧
    Integrable (radicalAverage F h μR E) (νN.restrict slice) ∧
    (∫ q, radicalAverage F h μR E q ∂νN.restrict slice) =
      c.toReal • (∫ z, E z ∂νH.restrict (projection h F ⁻¹' slice)) := by
  dsimp only
  let E := sectionIntegrand F ell f Wtest weight
  let slice := Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t a
  let Aabs := radicalAverage F h μR (fun z => (‖E z‖ : ℂ))
  have hEc := sectionIntegrand_continuous F ell f Wtest weight hW hw
  obtain ⟨_, hAabsc⟩ := sectionAverages_continuous F ell f Wtest weight μR hW hw
  let := hνN.regular
  let := leftQuotient_locallyCompactSpace (upperUnipotent (t + 1) F)
  let := Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap (upperUnipotent (t + 1) F))
  have hslice : IsClopen slice := Langlands.AllField.RankinSelberg.isClopen_determinantSlice _ t a
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
  obtain ⟨_, _, _, _, _, _, htower⟩ := twoBlockUnipotentQuotientIntegration F t m h
  obtain ⟨_, _, κ, hκfin, hκ, htowerR⟩ := htower μR
  let := hκfin
  have hfiber : ∀ g : GeneralLinear (t + 1) F,
      Integrable (fun x => E (fiberPoint h F x g)) μR := by
    intro g
    simpa only [E, sectionIntegrand_fiberPoint] using
      ((hraw g).const_mul (Wtest.val g)).mul_const (weight (Quotient.mk _ g))
  have hκfiber : ∀ q, Integrable E (κ q) := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [hκ g]
      have hcont : Continuous (fun x => fiberPoint h F x g) :=
        continuous_quotient_mk'.comp
          ((TwoBlockJacquet.continuous_upperRadical h F).mul continuous_const)
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

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
