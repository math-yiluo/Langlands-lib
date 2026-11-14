import Langlands.Representation.RankinSelberg.TwoBlockDominantUpperSliceAnalysis
import Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement
import Langlands.AllField.Representation.RankinSelberg.NormalizedCompactIntegrationProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantJacquetSeries
import Langlands.AllField.Representation.RankinSelberg.UnequalRankAnalyticProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankDeterminantSlices
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement
/-!
# Upper determinant-slice analysis for the dominant first-block identity

Internal consequences of the ordinary Jacquet convergence and realization,
the unequal-rank finite expansion, and the JPSS unequal-rank analytic theorem.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding UpperSliceConverges continuous_diagonalIntegrand continuous_upperAverage exists_uniformOrdinaryJacquetRealization instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsTopologicalGroupGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_rectangularBorelMeasure rectangularBorelMeasure upperSliceConverges
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW uS

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance (d : ℕ) : IsTopologicalGroup (GeneralLinear d F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup d
local instance (d : ℕ) : LocallyCompactSpace (GeneralLinear d F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace d
local instance (d : ℕ) : SecondCountableTopology (GeneralLinear d F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology d
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F) :=
  borel (GeneralLinear (n + 1) F)
local instance (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F) :=
  borel (upperUnipotent (n + 1) F)
local instance (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F) :=
  borel (LeftUnipotentQuotient n F)
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩

/-- The supplied finite product Haar measure in the Borel measurable structure
used by the determinant coefficient API. -/
def rectangularBorelMeasure (ν : AdditiveHaarMeasure F) (a b : ℕ) :
    @Measure (Matrix (Fin a) (Fin b) F) (borel _) := by
  have hB : (inferInstance : MeasurableSpace (Matrix (Fin a) (Fin b) F)) =
      borel _ :=
    @BorelSpace.measurable_eq _ _ _
      (inferInstanceAs (BorelSpace (Fin a → Fin b → F)))
  exact hB ▸ rectangularMeasure ν a b

private theorem integrable_measureTransport {X : Type*} {m₁ m₂ : MeasurableSpace X}
    (hm : m₁ = m₂) (μ : @Measure X m₁) (f : X → ℂ)
    (hf : @Integrable ℂ _ _ X m₁ f μ) :
    @Integrable ℂ _ _ X m₂ f (hm ▸ μ) := by
  cases hm
  exact hf

/-- Transport Schwartz integrability along equality of the product and Borel
measurable structures, without a measure map or rescaling. -/
theorem integrable_rectangularBorelMeasure (ν : AdditiveHaarMeasure F)
    (a b : ℕ) (φ : SchwartzBruhat (Matrix (Fin a) (Fin b) F)) :
    Integrable (φ : _ → ℂ) (rectangularBorelMeasure F ν a b) := by
  have hB : (inferInstance : MeasurableSpace (Matrix (Fin a) (Fin b) F)) =
      borel _ :=
    @BorelSpace.measurable_eq _ _ _
      (inferInstanceAs (BorelSpace (Fin a → Fin b → F)))
  exact integrable_measureTransport hB (rectangularMeasure ν a b) φ
    (Langlands.AllField.RankinSelberg.UnequalRankReduction.padic_rectangular_schwartz_integrable
      F (⟨⟩ : LocalFieldData F) a b ν φ)

section Jacquet

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- One ordinary Jacquet realization, including zero supplied block functionals,
chosen before all quotient measures and tests. -/
theorem exists_uniformOrdinaryJacquetRealization
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) :
    ∃ C : ℝ, ∀ u : ℝ, C < u →
      let σ := twoBlockOppositeTwistBlocks F m τ u
      let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
      let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
      (∀ f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ,
        Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ellu i).val) μR f) ∧
      ∃ J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ),
        ((∀ i, (ell i).val ≠ 0) → J.val ≠ 0) ∧
        ∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ) (g : GeneralLinear (t + 1) F),
          J.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ g f) =
            Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ (fun i => (ellu i).val) μR f g := by
  obtain ⟨C, hC⟩ := Langlands.AllField.RankinSelberg.TwoBlockConvergence.exists_bound_isAbsIntegrable_of_factorization
    F h ψ ν.val τ hτ ell (Langlands.AllField.RankinSelberg.TwoBlockConvergence.exists_radical_factorization F h)
  refine ⟨C, fun u hu => ⟨hC u hu, ?_⟩⟩
  let σ := twoBlockOppositeTwistBlocks F m τ u
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
  let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
  have hint : ∀ f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ,
      Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrableAt ψ (fun i => (ellu i).val) μR f 1 :=
    fun f => hC u hu f 1
  let J := Langlands.AllField.RankinSelberg.TwoBlockOrdinaryJacquet.ordinaryJacquetFunctional F h ψ σ
    (fun i => (ellu i).val) μR hint
  refine ⟨⟨J, Langlands.AllField.RankinSelberg.TwoBlockOrdinaryJacquet.ordinaryJacquetFunctional_mem F h ψ σ
    (fun i => (ellu i).val) (fun i => (ellu i).property) μR hint⟩, ?_, ?_⟩
  · intro hell
    exact Langlands.AllField.RankinSelberg.TwoBlockOrdinaryJacquet.ordinaryJacquetFunctional_ne_zero F h ψ σ
      (fun i => (ellu i).val)
      (fun i => ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff
        F m τ u i _).mpr (hτ i)).1.1) hell μR hint
  · exact fun f g =>
      Langlands.AllField.RankinSelberg.TwoBlockOrdinaryJacquet.ordinaryJacquetFunctional_inducedRep F h ψ σ
        (fun i => (ellu i).val) μR hint g f

end Jacquet

section Upper

variable {n : ℕ} (j k : ℕ) (ψ : UnitaryAdditiveCharacter F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {S : Type uS} [AddCommGroup S] [Module ℂ S]
  (π : Representation ℂ (GeneralLinear (n + (j + k + 1) + 1) F) V)
  (σ : Representation ℂ (GeneralLinear (n + 1) F) S)
  (lambda : glFunctionals ψ (n + (j + k + 1)) π)
  (J : glInverseFunctionals ψ n σ)
  (Wtest : (coefficientModel π lambda).toSubmodule)
  (Wjac : (coefficientModel σ J).toSubmodule)

private theorem coefficient_zero {d : ℕ}
    {θ : upperUnipotent (d + 1) F →* ℂˣ}
    (ρ : Representation ℂ (GeneralLinear (d + 1) F) V)
    (ell : functionals (upperUnipotent (d + 1) F) θ ρ)
    (hell : ell.val = 0) (W : (coefficientModel ρ ell).toSubmodule)
    (g : GeneralLinear (d + 1) F) : W.val.val g = 0 := by
  obtain ⟨v, rfl⟩ := modelMap_surjective ρ ell W
  change ell.val (ρ g v) = 0
  rw [hell, LinearMap.zero_apply]

private theorem continuous_appendIdentity (d e : ℕ) :
    Continuous (appendIdentity (F := F) d e) := by
  have hv : Continuous (fun g : GeneralLinear (d + 1) F =>
      (appendIdentity d e g).val) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro l
    simp only [appendIdentity_entry]
    split_ifs
    · exact Units.continuous_val.matrix_elem _ _
    all_goals exact continuous_const
  apply Units.continuous_iff.mpr
  exact ⟨hv, by simpa only [Function.comp_def, map_inv] using hv.comp continuous_inv⟩

/-- The diagonal term of the finite rectangular expansion is continuous,
with the full original rank-gap exponent. -/
theorem continuous_diagonalIntegrand (hπ : IsSmooth π) (hσ : IsSmooth σ) (s : ℂ) :
    Continuous (unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      j k Wtest.val Wjac.val s 0) := by
  have hW : Continuous Wtest.val.val := by
    obtain ⟨v, rfl⟩ := modelMap_surjective π lambda Wtest
    exact (matrixCoefficient_isLocallyConstant π lambda.val v (hπ v)).continuous
  have hW' : Continuous Wjac.val.val := by
    obtain ⟨v, rfl⟩ := modelMap_surjective σ J Wjac
    exact (matrixCoefficient_isLocallyConstant σ J.val v (hσ v)).continuous
  have hdet : Continuous (fun g : GeneralLinear (n + 1) F =>
      normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det g.val)) :=
    (NNReal.continuous_coe.comp (⟨⟩ : LocalFieldData F).continuous_normalizedAbsHom).comp
      Units.continuous_val.matrix_det
  have hw : Continuous (fun g : GeneralLinear (n + 1) F =>
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
        (s - ((j + k + 1 : ℕ) : ℂ) / 2)) :=
    (Complex.continuous_ofReal.comp hdet).cpow continuous_const
      (fun g => Complex.ofReal_mem_slitPlane.mpr
        ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).pos g.det_ne_zero))
  apply (leftQuotient_isOpenQuotientMap
    (upperUnipotent (n + 1) F)).isQuotientMap.continuous_iff.mpr
  change Continuous (fun g => Wtest.val.val (unequalRankMatrix j k g 0) *
    Wjac.val.val g * determinantWeight _ g _)
  simp only [UnequalRankReduction.unequalRankMatrix_at_zero]
  exact ((hW.comp (continuous_appendIdentity F n (j + k + 1))).mul hW').mul hw

/-- Finite Schwartz expansion gives a continuous rectangle average for every
spectral parameter, independently of outer convergence. -/
theorem continuous_upperAverage
    (hπ : IsOfWhittakerType (n + (j + k + 1))
      (standardCharacter ψ (n + (j + k + 1))) π)
    (hσ : IsSmooth σ) (ν : AdditiveHaarMeasure F) (s : ℂ) :
    Continuous (unequalRankAverage F j k ψ
      (rectangularBorelMeasure F ν j (n + 1)) Wtest.val Wjac.val s) := by
  classical
  by_cases hfirst : lambda.val = 0
  · have hz : unequalRankAverage F j k ψ (rectangularBorelMeasure F ν j (n + 1))
        Wtest.val Wjac.val s = 0 := by
      funext q
      induction q using Quotient.inductionOn with
      | h g =>
        simp [unequalRankAverage, unequalRankIntegrand_mk,
          coefficient_zero F π lambda hfirst Wtest]
    rw [hz]
    exact continuous_const
  obtain ⟨d, φ, fs, he⟩ := unequalRankFiniteExpansion F (⟨⟩ : LocalFieldData F)
    n j k ψ V π hπ lambda hfirst Wtest
    (unequalRankCompactSupport F (⟨⟩ : LocalFieldData F) n j k
      ψ V π hπ lambda hfirst Wtest)
  have hφ (i : Fin d) : Integrable (φ i) (rectangularBorelMeasure F ν j (n + 1)) :=
    integrable_rectangularBorelMeasure F ν j (n + 1) (φ i)
  have heq : unequalRankAverage F j k ψ (rectangularBorelMeasure F ν j (n + 1))
      Wtest.val Wjac.val s =
      fun q => ∑ i : Fin d,
        unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          j k (fs i).val Wjac.val s 0 q *
            (∫ x, φ i x ∂rectangularBorelMeasure F ν j (n + 1)) := by
    funext q
    unfold unequalRankAverage
    simp_rw [UnequalRankReduction.integrand_of_finite_expansion ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) j k d Wtest.val Wjac.val
      (fun i => (φ i : _ → ℂ)) (fun i => (fs i).val) he]
    rw [integral_finsetSum _ (fun i _ => (hφ i).const_mul _)]
    simp only [integral_const_mul]
  rw [heq]
  exact continuous_finsetSum _ fun i _ =>
    (continuous_diagonalIntegrand F j k ψ π σ lambda J (fs i) Wjac hπ.1.1 hσ s).mul
      continuous_const

/-- Upper product-space convergence on every determinant slice. -/
def UpperSliceConverges
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F) (a : ℤ) : Prop :=
  Integrable (fun z : LeftUnipotentQuotient n F ×
      Matrix (Fin j) (Fin (n + 1)) F =>
    unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      j k Wtest.val Wjac.val 0 z.2 z.1)
    ((μ.restrict (determinantSlice (⟨⟩ : LocalFieldData F) n a)).prod
      (rectangularMeasure ν j (n + 1)))

/-- Restrict right-half-plane convergence to a slice and divide by its nonzero
constant spectral weight. This retains zero supplied functionals. -/
theorem upperSliceConverges
    (hπ : IsOfWhittakerType (n + (j + k + 1))
      (standardCharacter ψ (n + (j + k + 1))) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    [Measure.IsMulRightInvariant (unipotentHaar F n)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (hμ : IsCompatible (upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) μ)
    (ν : AdditiveHaarMeasure F) (a : ℤ) :
    UpperSliceConverges F j k ψ π σ lambda J Wtest Wjac μ ν a := by
  let : μ.Regular := hμ.regular
  let : T2Space (LeftUnipotentQuotient n F) :=
    leftQuotient_t2Space _ (UpperUnipotent.isClosed (R := F))
  let : LocallyCompactSpace (LeftUnipotentQuotient n F) :=
    leftQuotient_locallyCompactSpace _
  let : SecondCountableTopology (LeftUnipotentQuotient n F) :=
    Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
  let : SigmaFinite μ := inferInstance
  by_cases hfirst : lambda.val = 0
  · unfold UpperSliceConverges
    have hz (z : LeftUnipotentQuotient n F ×
        Matrix (Fin j) (Fin (n + 1)) F) :
        unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          j k Wtest.val Wjac.val 0 z.2 z.1 = 0 := by
      induction z.1 using Quotient.inductionOn with
      | h g =>
        simp [unequalRankIntegrand_mk, coefficient_zero F π lambda hfirst Wtest]
    simp only [hz]
    exact integrable_zero _ _ _
  by_cases hJ : J.val = 0
  · unfold UpperSliceConverges
    have hz (z : LeftUnipotentQuotient n F ×
        Matrix (Fin j) (Fin (n + 1)) F) :
        unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          j k Wtest.val Wjac.val 0 z.2 z.1 = 0 := by
      induction z.1 using Quotient.inductionOn with
      | h g =>
        simp [unequalRankIntegrand_mk, coefficient_zero F σ J hJ Wjac]
    simp only [hz]
    exact integrable_zero _ _ _
  obtain ⟨C, hC⟩ := (unequalRankAnalytic F (⟨⟩ : LocalFieldData F) n j k
    ψ μ hμ ν V S π σ hπ hσ lambda J hfirst hJ).1 Wtest Wjac
  let s : ℂ := (C + 1 : ℝ)
  have hs : UnequalRankConverges ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      j k μ (rectangularMeasure ν j (n + 1)) Wtest.val Wjac.val s :=
    hC s (by dsimp [s]; simp)
  let slice := determinantSlice (⟨⟩ : LocalFieldData F) n a
  have hslice : MeasurableSet slice :=
    measurableSet_determinantSlice (⟨⟩ : LocalFieldData F) n a
  have hi : Integrable (fun z : LeftUnipotentQuotient n F ×
      Matrix (Fin j) (Fin (n + 1)) F =>
        unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          j k Wtest.val Wjac.val s z.2 z.1)
      ((μ.restrict slice).prod (rectangularMeasure ν j (n + 1))) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hs.restrict
  have heq : (fun z : LeftUnipotentQuotient n F ×
      Matrix (Fin j) (Fin (n + 1)) F =>
        unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          j k Wtest.val Wjac.val s z.2 z.1) =ᵐ[
            (μ.restrict slice).prod (rectangularMeasure ν j (n + 1))]
      fun z => unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        j k Wtest.val Wjac.val 0 z.2 z.1 *
          spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^ a := by
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (hslice.prod MeasurableSet.univ)] with z hz
    exact unequalRankIntegrand_eq_mul_spectralPoint_zpow
      F j k ψ Wtest.val Wjac.val a z.1 hz.1 s z.2
  have hc : spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^ a ≠ 0 :=
    zpow_ne_zero a (spectralPoint_ne_zero_of_pos
      (Nat.zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s)
  exact (integrable_mul_const_iff (IsUnit.mk0 _ hc) _).mp (hi.congr heq)

end Upper

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
