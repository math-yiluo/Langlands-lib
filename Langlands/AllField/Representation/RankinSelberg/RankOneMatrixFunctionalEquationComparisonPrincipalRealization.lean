import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalRealization
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierAveraging
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalWeighted
/-! # Actual bi-smooth realization on the uniform principal box -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg.RankOneBox hiding ModelBoxConditions PrincipalModelRealization averagedModelCoefficient_eq_of_left_invariant box boxCoefficientBorelSpace boxCoefficientLocalField boxCoefficientMeasurableSpace boxCoefficientTopology boxCoefficientValuativeRel boxCoefficient_extraction_of_principalLevel boxCoefficient_mul_principalLevel boxCoefficient_point boxComparisonVolume boxConvergenceBorelSpace boxConvergenceLocalField boxConvergenceMeasurableSpace boxConvergenceSecondCountable boxConvergenceT2 boxConvergenceTopology boxConvergenceUnipotentBorel boxConvergenceUnipotentMeasurable boxConvergenceUnitsBorel boxConvergenceUnitsMeasurable boxConvergenceUnitsSecondCountable boxConvergenceValuativeRel boxEntry boxExtractionConstant boxExtractionConstant_pos boxLatticeCentre boxLatticeTest boxLatticeTest_apply boxLatticeTest_eq_compactOpenIndicator boxSupport boxVolumeBorelSpace boxVolumeLocalField boxVolumeMeasurableSpace boxVolumeTopology boxVolumeUnipotentBorel boxVolumeUnipotentMeasurable boxVolumeValuativeRel box_comparison_of_integrable box_eq_pi box_eq_rectangularLatticeCoset box_matrixIntegrand_eq_of_eq_on_box coe_unitLevel continuous_determinantWeight continuous_glModelFunction continuous_principalAverage continuous_rankOneEmbedding continuous_unipotent_entry cutoffUnipotent_mem_principalLevel determinantRankOne_point determinantWeight_mul_of_norm_one determinantWeight_rankOneEmbedding determinantWeighted_equivariant diagonalUnits_mem_principalLevel exists_box_averagedModelCoefficient_eq exists_box_constant exists_mem_principalLevel_mul_inv_upper exists_point_mul_of_mem_box exists_principalModelRealization glLocallyCompact glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integer_of_mem_principalLevel integral_eq_of_support integral_param_of_eq inv_sub_one_mem_levelSet isCompact_box isCompact_boxEntry isCompact_unipotentBox isOpen_box isOpen_boxEntry isOpen_boxSupport isOpen_torusBox isOpen_unipotentBox isOpen_unitLevel levelSet_eq_additiveLattice lintegral_enorm_eq_of_support lintegral_param_of_eq matrixIntegrand_mul_principalLevel matrixIntegrand_point matrixLocallyCompact measurableSet_integralSubgroup measurePreserving_rshift mem_box_iff mem_box_unipotent_mul_iff mem_torusBox_of_mem_box mem_unitLevel_iff modelFunction_eq_determinantRankOne_of_mem_box modelFunction_eq_determinantRankOne_of_mem_box_of_le mul_mem_box mul_mem_box_iff mul_mem_box_iff_of_le mul_mem_box_of_le mul_sub_one_mem_levelSet one_mem_box one_mem_boxSupport one_mem_unipotentBox parameterBase_isMulLeftInvariant point_eq_mul principalAverage principalAverageGLBorel principalAverageGLLocallyCompact principalAverageGLMeasurable principalAverageGLSecondCountable principalAverageLocalField principalAverageMatrixLocallyCompact principalAverageT2 principalAverageTopology principalAverageValuativeRel principalAverage_box_integral principalAverage_equivariant principalAverage_extraction principalAverage_mul principalAveragingMeasure principalAveragingMeasure_ae_det_norm principalAveragingMeasure_ae_mem principalAveragingMeasure_finite principalAveragingMeasure_fixed principalAveragingMeasure_integral principalAveragingMeasure_mass principalAveragingMeasure_weighted_integral principalLevel_firstRow principalLevel_le_integral principalLevel_mass_pos principalMeasure_extraction principalMeasure_weighted_extraction principalRealizationGLBorel principalRealizationGLMeasurable principalRealizationLocalField principalRealizationTopology principalRealizationValuativeRel principalWeightedGLBorel principalWeightedGLMeasurable principalWeightedLocalField principalWeightedScalarAverage principalWeightedTopology principalWeightedValuativeRel rankOneEmbedding_eq_point rankOneModelValues_subset rankOneModel_convergesOnRight_of_matrix rankOne_support_of_principalLevel restrict_boxSupport_lt_top restrict_boxSupport_pos standardCharacter_eq_one tailMeasure_torusBox tailMeasure_torusBox_lt_top tailMeasure_torusBox_pos torusBox torusBox_eq_pi torusFactor_mem uniformBoxGLBorel uniformBoxGLMeasurable uniformBoxLocalField uniformBoxSecondCountable uniformBoxT2 uniformBoxTopology uniformBoxUnipotentBorel uniformBoxUnipotentMeasurable uniformBoxUnitsBorel uniformBoxUnitsMeasurable uniformBoxUnitsSecondCountable uniformBoxValuativeRel uniformBox_mul_principalLevel uniform_box_extraction unipotentBox unipotentBox_eq_entry_preimage unipotentBox_subset unipotentHaar_unipotentBox_lt_top unipotentHaar_unipotentBox_lt_top_all unipotentHaar_unipotentBox_pos unipotentLocallyCompact unipotentSecondCountable unipotent_mul_rankOne_apply unipotent_mul_rankOne_apply_zero unitLevel unitLevel_le_integralUnits unitLevel_measure_le unitLevel_measure_pos unitsSecondCountable weight_smul_integrand
open Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rankOne_blockZero_exists_ne_zero singleton_modulus_real unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement isClopen_rectangularLatticeCoset isCompact_rectangularLatticeCoset mem_rectangularLatticeCoset padicLatticeGeometry padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists rectangularLatticeCoset rectangularLatticeCosetTest rectangularLatticeCosetTest_apply
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.Conductor
open Langlands.RankinSelberg.RankOneIwasawa hiding ColBound abv_det_eq_one ae_outerMeasure_mem colBound_of_inv colBound_zero congruenceGroup congruenceGroup_le_integral conj_mem_congruenceGroup continuous_det_units continuous_point continuous_torusCoord continuous_torusModulus continuous_weight det_point det_unipotent_mul determinantWeight_diagPoint diagPoint elemUnipotent elemUnipotent_val exists_congruenceGroup_le exists_cornerSchwartz exists_lattice_nontrivial exists_lattice_subset exists_mem_lattice exists_mem_matLattice exists_ne_zero_of_unipotentTransform_ne_zero exists_schwartz_congruence glLocallyCompact glLocallyCompactU glOneMeasure glOneMeasure_sigmaFinite glSecondCountable glSecondCountableU instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instIsNonarchimedeanLocalFieldCarrier_3 instIsNonarchimedeanLocalFieldCarrier_4 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instMeasurableSpaceUnitsCarrier instMeasurableSpaceUnitsCarrier_1 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instTopologicalSpaceCarrier_3 instTopologicalSpaceCarrier_4 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 instValuativeRelCarrier_3 instValuativeRelCarrier_4 integralSet integralSubgroup_mem_matLattice integral_matrixIntegrand_unfold integral_mul_matLattice inv_mem_lattice_of_notMem inv_mem_of_colBound isCompact_lattice isOpen_congruenceGroup isOpen_lattice isOpen_matLattice iwasawaMeasure iwasawaMeasure_point_preimage iwasawaMeasure_sFinite lattice_mono lattice_mul map_iwasawaMeasure_prod map_unfoldedMeasure matLattice matLattice_basis matLattice_mono matLattice_mul matLattice_mul_integral matrixIntegrand_unfoldedPoint matrixLocallyCompact matrixLocallyCompactU measurable_point measurable_unfoldedPoint measurePreserving_shift mem_lattice_zero_iff mem_matLattice mem_matLattice_of_support mul_sub_one_mem one_add_mem_lattice_zero one_add_single_apply one_mem_lattice_zero outerMeasure outerMeasure_sFinite parameterBase_isMulLeftInvariant parameterMeasure parameterMeasure_eq_prod parameterMeasure_sigmaFinite schwartzOfLattice schwartzOfLattice_apply schwartz_invariance schwartz_support_bound standardCharacter_elemUnipotent tailMeasure tailMeasure_sigmaFinite torusModulus torusModulus_apply torusModulus_cons_one torusModulus_eq_one unfoldedMeasure unfoldedMeasure_eq unfoldedPoint unfoldedPoint_eq unipotentConj_map unipotentLocallyCompact unipotentLocallyCompactU unipotentSecondCountable unipotentSecondCountableU unipotentTransform unipotentTransform_diag_bounds unipotentTransform_eq_zero_of_shift unipotentTransform_mul_right unipotent_col_zero unipotent_mul_single_zero unitsSecondCountable weight weight_apply weight_glOne weight_split
open Langlands.AllField.RankinSelberg.RankOneIwasawa
open Langlands.RankinSelberg.UnequalRankMirabolicUnitTest
open scoped NNReal ENNReal

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance principalRealizationGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance principalRealizationGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

local notation "𝓛" => (Langlands.LocalFieldData.additiveLattice (⟨⟩ : LocalFieldData F))
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable (ψ : UnitaryAdditiveCharacter F) {m : ℕ} {V : Type uV}
  [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V)
  (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)

/-- The determinant reduction on a model box only needs q ≤ A. -/
theorem modelFunction_eq_determinantRankOne_of_mem_box_of_le {A q : ℤ} {a : ℕ}
    (ha : 0 < a) (hqA : q ≤ A)
    (hL : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ j, j ≠ 0 →
      y.val 0 j ∈ 𝓛 (q - A))
    (hψ : ∀ z ∈ 𝓛 q, ψ z = 1)
    (hlev : ∀ z ∈ levelSet F a, z ∈ 𝓛 q)
    (hstab : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g)
    (hDstab : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * determinantRankOne (m + 1) y) =
        glModelFunction ψ (m + 1) σ ℓ w g)
    {g : Langlands.GeneralLinear (m + 1 + 1) F}
    (hg : g.val ∈ box F A q a) :
    glModelFunction ψ (m + 1) σ ℓ w g =
      glModelFunction ψ (m + 1) σ ℓ w (determinantRankOne (m + 1) g) := by
  obtain ⟨y, hy, hb⟩ := exists_mem_principalLevel_mul_inv_upper F ha hg
  obtain ⟨⟨⟨g₁, t⟩, u⟩, hx⟩ := exists_point_eq (g * y⁻¹) hb
  have hbox : (point ((g₁, t), u)).val ∈ box F A q a := by
    rw [hx, Units.val_mul]
    exact (mul_mem_box_iff_of_le F hqA hL g.val (inv_mem hy)).2 hg
  have ht := torusFactor_mem F ha (mem_torusBox_of_mem_box F hbox)
  have hu : u ∈ unipotentBox F q a := by
    have h := hbox
    rw [point_eq_mul F, Units.val_mul,
      mul_mem_box_iff_of_le F hqA hL _ ht, mem_box_unipotent_mul_iff] at h
    exact h.2
  have hW : glModelFunction ψ (m + 1) σ ℓ w (point ((g₁, t), u)) =
      glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g₁) := by
    rw [point_eq_mul F, hstab _ ht, glModelFunction_equivariance,
      standardCharacter_eq_one F ψ hψ hlev hu, one_mul]
    rfl
  calc
    glModelFunction ψ (m + 1) σ ℓ w g =
        glModelFunction ψ (m + 1) σ ℓ w (g * y⁻¹) := (hstab _ (inv_mem hy) g).symm
    _ = glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g₁) := by rw [← hx]; exact hW
    _ = glModelFunction ψ (m + 1) σ ℓ w
        (determinantRankOne (m + 1) (g * y⁻¹)) := by
      rw [← hx, determinantRankOne_point F]
      rfl
    _ = glModelFunction ψ (m + 1) σ ℓ w (determinantRankOne (m + 1) g) := by
      rw [map_mul, hDstab _ (inv_mem hy)]

/-- One actual normalized left-average coefficient realizes the original model
vector on the precise uniform extraction box and retains its right principal
invariance. The compact averaging subgroup fixes the full matrix test. -/
def PrincipalModelRealization (hσ : IsSmooth σ) (a : ℕ)
    (K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F))) : Prop :=
  let c := (⟨⟩ : LocalFieldData F).additiveConductor ψ
  let f := Langlands.AllField.GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w
  0 < a ∧ 0 ≤ c + a ∧
    (∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g) ∧
    (∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * determinantRankOne (m + 1) y) =
        glModelFunction ψ (m + 1) σ ℓ w g) ∧
    (∀ k ∈ K,
      (∀ M, boxLatticeTest F (c + a) c a (k.val * M) = boxLatticeTest F (c + a) c a M) ∧
        abv (Matrix.det k.val) = 1) ∧
    (∀ g : Langlands.GeneralLinear (m + 1 + 1) F,
      g.val ∈ box F (c + a) c a → f.val g = glModelFunction ψ (m + 1) σ ℓ w g) ∧
    (∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ g, f.val (g * y) = f.val g)

/-- Every original smooth model vector has such a realization at arbitrary
additive conductor, with independent field and representation universes. -/
theorem exists_principalModelRealization (hσ : IsSmooth σ) :
    ∃ (a : ℕ) (K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F))
      (hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F))),
      PrincipalModelRealization F ψ σ ℓ w hσ a K hK := by
  let c := (⟨⟩ : LocalFieldData F).additiveConductor ψ
  obtain ⟨Kw, hKw⟩ := glModel_isSmooth ψ (m + 1) σ hσ ℓ w
  let KD := Kw.comap (determinantRankOne (m + 1)) (continuous_determinantRankOne (m + 1))
  obtain ⟨a₀, ha₀, ha₀U⟩ := exists_pos_principalLevelOpenSubgroup_subset F (m + 1)
    ((Kw ⊓ KD).isOpen.mem_nhds (one_mem _))
  let a : ℕ := a₀ + (-c).toNat + 1
  have ha : 0 < a := by dsimp [a]; omega
  have hA : 0 ≤ c + a := by
    have h := Int.self_le_toNat (-c)
    dsimp [a]
    omega
  have hsuba : principalLevelSubgroup F (m + 1) a ≤
      principalLevelSubgroup F (m + 1) a₀ :=
    principalLevelSubgroup_antitone F (m + 1) (by dsimp [a]; omega)
  have hmemU : ∀ y ∈ principalLevelSubgroup F (m + 1) a,
      y ∈ Kw ⊓ KD := fun y hy => ha₀U (hsuba hy)
  have hstab : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g := by
    intro y hy g
    have hfix : glModelRepresentation ψ (m + 1) σ ℓ y w = w := hKw ⟨y, (hmemU y hy).1⟩
    rw [← glModelFunction_translate, hfix]
  have hDstab : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * determinantRankOne (m + 1) y) =
        glModelFunction ψ (m + 1) σ ℓ w g := by
    intro y hy g
    have hfix : glModelRepresentation ψ (m + 1) σ ℓ (determinantRankOne (m + 1) y) w = w :=
      hKw ⟨determinantRankOne (m + 1) y, (hmemU y hy).2⟩
    rw [← glModelFunction_translate, hfix]
  have hL : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ j, j ≠ 0 →
      y.val 0 j ∈ 𝓛 (c - (c + a)) := fun _ hy => principalLevel_firstRow F c a hy
  have hψ : ∀ z ∈ 𝓛 c, ψ z = 1 :=
    ((⟨⟩ : LocalFieldData F).additiveTrivialAt_iff_le_conductor ψ c).2 le_rfl
  have hlev : ∀ z ∈ levelSet F a, z ∈ 𝓛 c := by
    intro z hz
    rw [levelSet_eq_additiveLattice F] at hz
    exact lattice_mono F (by omega) hz
  let Φ := boxLatticeTest F (n := m + 1) (c + a) c a
  obtain ⟨K₀, hK₀, hΦ⟩ := Langlands.AllField.GodementJacquet.Padic.exists_compactOpen_matrixTest_invariant F Φ
  obtain ⟨K, hK, hsub⟩ := (⟨⟩ : LocalFieldData F).generalLinearCompactOpen (m + 1 + 1)
    (((K₀ ⊓ KD : OpenSubgroup _) : Set _)) ((K₀ ⊓ KD).isOpen.mem_nhds (one_mem _))
  refine ⟨a, K, hK, ha, hA, hstab, hDstab, (fun k hk => hΦ k (hsub hk).1), ?_, ?_⟩
  · intro g hg
    apply averagedModelCoefficient_eq_of_left_invariant F ψ σ ℓ w hσ K hK g
    intro k hk
    have hkg : (k * g).val ∈ box F (c + a) c a := by
      have h := (hΦ k (hsub hk).1).1 g.val
      dsimp only [Φ] at h
      simp only [boxLatticeTest_apply] at h
      rw [Set.indicator_of_mem hg] at h
      by_contra hn
      change k.val * g.val ∉ box F (c + a) c a at hn
      rw [Set.indicator_of_notMem hn] at h
      exact zero_ne_one h
    rw [modelFunction_eq_determinantRankOne_of_mem_box_of_le F ψ σ ℓ w ha (by omega) hL hψ hlev
        hstab hDstab hkg,
      modelFunction_eq_determinantRankOne_of_mem_box_of_le F ψ σ ℓ w ha (by omega) hL hψ hlev
        hstab hDstab hg, map_mul]
    have hcomm : determinantRankOne (m + 1) k * determinantRankOne (m + 1) g =
        determinantRankOne (m + 1) g * determinantRankOne (m + 1) k := by
      unfold determinantRankOne
      change Iwasawa.diagonalUnits _ * Iwasawa.diagonalUnits _ =
        Iwasawa.diagonalUnits _ * Iwasawa.diagonalUnits _
      rw [← map_mul, ← map_mul, mul_comm]
    rw [hcomm, ← glModelFunction_translate]
    have hfix : glModelRepresentation ψ (m + 1) σ ℓ (determinantRankOne (m + 1) k) w = w :=
      hKw ⟨determinantRankOne (m + 1) k, (hsub hk).2⟩
    rw [hfix]
  · intro y hy g
    simp only [Langlands.AllField.GodementJacquet.Padic.averagedModelCoefficient_apply,
      GodementJacquet.normalizedLeftAverage]
    congr 1
    apply setIntegral_congr_fun K.isOpen.measurableSet
    intro k hk
    change glModelFunction ψ (m + 1) σ ℓ w (k * (g * y)) =
      glModelFunction ψ (m + 1) σ ℓ w (k * g)
    rw [← mul_assoc, hstab y hy]

end Langlands.AllField.RankinSelberg.RankOneBox
