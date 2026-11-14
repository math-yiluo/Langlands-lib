import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUniformBox
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxFourier
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxVolume
/-! # Uniform box extraction at arbitrary additive conductor -/

noncomputable section

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg.RankOneBox hiding ModelBoxConditions averagedModelCoefficient_eq_of_left_invariant box boxCoefficientBorelSpace boxCoefficientLocalField boxCoefficientMeasurableSpace boxCoefficientTopology boxCoefficientValuativeRel boxCoefficient_extraction_of_principalLevel boxCoefficient_mul_principalLevel boxCoefficient_point boxComparisonVolume boxConvergenceBorelSpace boxConvergenceLocalField boxConvergenceMeasurableSpace boxConvergenceSecondCountable boxConvergenceT2 boxConvergenceTopology boxConvergenceUnipotentBorel boxConvergenceUnipotentMeasurable boxConvergenceUnitsBorel boxConvergenceUnitsMeasurable boxConvergenceUnitsSecondCountable boxConvergenceValuativeRel boxEntry boxExtractionConstant boxExtractionConstant_pos boxLatticeCentre boxLatticeTest boxLatticeTest_apply boxLatticeTest_eq_compactOpenIndicator boxSupport boxVolumeBorelSpace boxVolumeLocalField boxVolumeMeasurableSpace boxVolumeTopology boxVolumeUnipotentBorel boxVolumeUnipotentMeasurable boxVolumeValuativeRel box_comparison_of_integrable box_eq_pi box_eq_rectangularLatticeCoset box_matrixIntegrand_eq_of_eq_on_box coe_unitLevel continuous_determinantWeight continuous_glModelFunction continuous_rankOneEmbedding continuous_unipotent_entry cutoffUnipotent_mem_principalLevel determinantRankOne_point diagonalUnits_mem_principalLevel exists_box_averagedModelCoefficient_eq exists_box_constant exists_mem_principalLevel_mul_inv_upper exists_point_mul_of_mem_box glLocallyCompact glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integer_of_mem_principalLevel integral_eq_of_support integral_param_of_eq inv_sub_one_mem_levelSet isCompact_box isCompact_boxEntry isCompact_unipotentBox isOpen_box isOpen_boxEntry isOpen_boxSupport isOpen_torusBox isOpen_unipotentBox isOpen_unitLevel levelSet_eq_additiveLattice lintegral_enorm_eq_of_support lintegral_param_of_eq matrixIntegrand_mul_principalLevel matrixIntegrand_point matrixLocallyCompact measurableSet_integralSubgroup measurePreserving_rshift mem_box_iff mem_box_unipotent_mul_iff mem_torusBox_of_mem_box mem_unitLevel_iff modelFunction_eq_determinantRankOne_of_mem_box mul_mem_box mul_mem_box_iff mul_mem_box_iff_of_le mul_mem_box_of_le mul_sub_one_mem_levelSet one_mem_box one_mem_boxSupport one_mem_unipotentBox parameterBase_isMulLeftInvariant point_eq_mul principalLevel_firstRow principalLevel_le_integral rankOneEmbedding_eq_point rankOneModelValues_subset rankOneModel_convergesOnRight_of_matrix rankOne_support_of_principalLevel restrict_boxSupport_lt_top restrict_boxSupport_pos standardCharacter_eq_one tailMeasure_torusBox tailMeasure_torusBox_lt_top tailMeasure_torusBox_pos torusBox torusBox_eq_pi torusFactor_mem uniformBoxGLBorel uniformBoxGLMeasurable uniformBoxLocalField uniformBoxSecondCountable uniformBoxT2 uniformBoxTopology uniformBoxUnipotentBorel uniformBoxUnipotentMeasurable uniformBoxUnitsBorel uniformBoxUnitsMeasurable uniformBoxUnitsSecondCountable uniformBoxValuativeRel uniform_box_extraction unipotentBox unipotentBox_eq_entry_preimage unipotentBox_subset unipotentHaar_unipotentBox_lt_top unipotentHaar_unipotentBox_lt_top_all unipotentHaar_unipotentBox_pos unipotentLocallyCompact unipotentSecondCountable unipotent_mul_rankOne_apply unipotent_mul_rankOne_apply_zero unitLevel unitLevel_le_integralUnits unitLevel_measure_le unitLevel_measure_pos unitsSecondCountable weight_smul_integrand
open Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rankOne_blockZero_exists_ne_zero singleton_modulus_real unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement isClopen_rectangularLatticeCoset isCompact_rectangularLatticeCoset mem_rectangularLatticeCoset padicLatticeGeometry padicRectangularHaarScaling padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists rectangularLatticeCoset rectangularLatticeCosetTest rectangularLatticeCosetTest_apply
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.Conductor
open Langlands.RankinSelberg.RankOneIwasawa hiding ColBound colBound_of_inv colBound_zero congruenceGroup congruenceGroup_le_integral conj_mem_congruenceGroup continuous_det_units continuous_point continuous_torusCoord continuous_torusModulus continuous_weight det_point elemUnipotent elemUnipotent_val exists_congruenceGroup_le exists_cornerSchwartz exists_lattice_nontrivial exists_lattice_subset exists_mem_lattice exists_mem_matLattice exists_ne_zero_of_unipotentTransform_ne_zero exists_schwartz_congruence glLocallyCompact glOneMeasure glOneMeasure_sigmaFinite glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instIsNonarchimedeanLocalFieldCarrier_3 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instTopologicalSpaceCarrier_3 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 instValuativeRelCarrier_3 integralSubgroup_mem_matLattice integral_mul_matLattice inv_mem_lattice_of_notMem inv_mem_of_colBound isCompact_lattice isOpen_congruenceGroup isOpen_lattice isOpen_matLattice iwasawaMeasure iwasawaMeasure_point_preimage iwasawaMeasure_sFinite lattice_mono lattice_mul map_iwasawaMeasure_prod map_unfoldedMeasure matLattice matLattice_basis matLattice_mono matLattice_mul matLattice_mul_integral matrixLocallyCompact measurable_point measurable_unfoldedPoint measurePreserving_shift mem_lattice_zero_iff mem_matLattice mem_matLattice_of_support mul_sub_one_mem one_add_mem_lattice_zero one_add_single_apply one_mem_lattice_zero parameterBase_isMulLeftInvariant parameterMeasure parameterMeasure_eq_prod parameterMeasure_sigmaFinite schwartzOfLattice schwartzOfLattice_apply schwartz_invariance schwartz_support_bound standardCharacter_elemUnipotent tailMeasure tailMeasure_sigmaFinite torusModulus torusModulus_apply torusModulus_cons_one torusModulus_eq_one unfoldedMeasure unfoldedPoint unipotentConj_map unipotentLocallyCompact unipotentSecondCountable unipotentTransform unipotentTransform_diag_bounds unipotentTransform_eq_zero_of_shift unipotentTransform_mul_right unipotent_col_zero unipotent_mul_single_zero unitsSecondCountable weight weight_apply weight_glOne weight_split
open Langlands.AllField.RankinSelberg.RankOneIwasawa
open Langlands.RankinSelberg.UnequalRankMirabolicUnitTest

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance uniformBoxT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance uniformBoxSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance uniformBoxGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance uniformBoxGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance uniformBoxUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance uniformBoxUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance uniformBoxUnitsMeasurable : MeasurableSpace Fˣ := borel _
local instance uniformBoxUnitsBorel : BorelSpace Fˣ := ⟨rfl⟩
local instance uniformBoxUnitsSecondCountable : SecondCountableTopology Fˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

local notation "𝓛" => (Langlands.LocalFieldData.additiveLattice (⟨⟩ : LocalFieldData F))

variable {n : ℕ}

theorem mul_mem_box_of_le {A q : ℤ} {a : ℕ} (hqA : q ≤ A)
    {X : Matrix (Fin (n + 1)) (Fin (n + 1)) F} (hX : X ∈ box F A q a)
    {y : Langlands.GeneralLinear (n + 1) F} (hy : y ∈ principalLevelSubgroup F n a)
    (hy0 : ∀ j, j ≠ 0 → y.val 0 j ∈ 𝓛 (q - A)) : X * y.val ∈ box F A q a := by
  obtain ⟨h0, h1, h2⟩ := (mem_box_iff F X).1 hX
  have hyO : ∀ i j, y.val i j ∈ 𝓛 0 := fun i j =>
    (mem_lattice_zero_iff F _).2 (integer_of_mem_principalLevel F hy i j)
  rw [mem_box_iff]
  refine ⟨?_, fun j hj => ?_, fun i hi j => ?_⟩
  · rw [Matrix.mul_apply]
    refine AddSubgroup.sum_mem _ fun l _ => ?_
    by_cases hl : l = 0
    · subst hl
      have h := lattice_mul F h0 (hyO 0 0)
      rwa [add_zero] at h
    · exact lattice_mono F (by omega) (lattice_mul F (h1 l hl) (hyO l 0))
  · rw [Matrix.mul_apply]
    refine AddSubgroup.sum_mem _ fun l _ => ?_
    by_cases hl : l = 0
    · subst hl
      have h := lattice_mul F h0 (hy0 j hj)
      rwa [add_sub_cancel] at h
    · have h := lattice_mul F (h1 l hl) (hyO l j)
      rwa [add_zero] at h
  · have hXy : X * y.val = (X - 1) * y.val + y.val := by
      rw [Matrix.sub_mul, Matrix.one_mul, sub_add_cancel]
    rw [hXy, Matrix.add_apply, add_sub_assoc]
    refine add_mem_levelSet ?_ (((mem_principalLevelSubgroup_iff y).1 hy).1 i j)
    rw [Matrix.mul_apply]
    exact sum_mem_levelSet _ fun l _ =>
      mul_mem_levelSet (by rw [Matrix.sub_apply]; exact h2 i hi l)
        (integer_of_mem_principalLevel F hy l j)

theorem mul_mem_box_iff_of_le {A q : ℤ} {a : ℕ} (hqA : q ≤ A)
    (hL : ∀ y ∈ principalLevelSubgroup F n a, ∀ j, j ≠ 0 → y.val 0 j ∈ 𝓛 (q - A))
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    {y : Langlands.GeneralLinear (n + 1) F}
    (hy : y ∈ principalLevelSubgroup F n a) :
    X * y.val ∈ box F A q a ↔ X ∈ box F A q a := by
  refine ⟨fun h => ?_, fun h => mul_mem_box_of_le F hqA h hy (hL y hy)⟩
  have h' := mul_mem_box_of_le F hqA h (inv_mem hy) (hL _ (inv_mem hy))
  rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at h'

/-- In actual strict upper-entry coordinates the box is a finite product of
compact scalar lattices, for every integer first-row level. -/
theorem unipotentBox_eq_entry_preimage (q : ℤ) (a : ℕ) :
    unipotentBox F (n := n) q a = (upperEntryCoordinates (n + 1)) ⁻¹'
      (Set.univ.pi fun ij : UpperEntryPair (n + 1) =>
        if ij.1.1 = 0 then (𝓛 q : Set F) else levelSet F a) := by
  ext u
  constructor
  · intro hu ij _
    simp only [upperEntryCoordinates_apply]
    by_cases hi : ij.1.1 = 0
    · rw [ite_eq_left hi, hi]
      exact hu.1 _ (by intro h; have := ij.2; rw [hi, h] at this; exact lt_irrefl _ this)
    · rw [ite_eq_right hi]
      have h := hu.2 _ hi ij.1.2
      rwa [Matrix.one_apply_ne ij.2.ne, sub_zero] at h
  · intro hu
    refine ⟨fun j hj => ?_, fun i hi j => ?_⟩
    · have h := hu ⟨(0, j), Fin.pos_of_ne_zero hj⟩ (Set.mem_univ _)
      simpa [upperEntryCoordinates_apply] using h
    · by_cases hij : i < j
      · have h := hu ⟨(i, j), hij⟩ (Set.mem_univ _)
        simpa only [Set.mem_preimage, upperEntryCoordinates_apply, ite_eq_right hi,
          Matrix.one_apply_ne hij.ne, sub_zero] using h
      · by_cases heq : i = j
        · subst j
          rw [UpperUnipotent.entry_diag, Matrix.one_apply_eq, sub_self]
          exact zero_mem_levelSet a
        · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm heq)
          rw [UpperUnipotent.entry_eq_zero u hji, Matrix.one_apply_ne heq, sub_self]
          exact zero_mem_levelSet a

theorem isCompact_unipotentBox (q : ℤ) (a : ℕ) :
    IsCompact (unipotentBox F (n := n) q a) := by
  rw [unipotentBox_eq_entry_preimage]
  apply (upperEntryCoordinates (n + 1)).isCompact_preimage.2
  apply isCompact_univ_pi
  intro ij
  split_ifs
  · exact isCompact_lattice F q
  · exact isCompact_levelSet a

/-- Finiteness holds at arbitrary conductor, including positive lattice levels. -/
theorem unipotentHaar_unipotentBox_lt_top_all (q : ℤ) (a : ℕ) :
    unipotentHaar F n (unipotentBox F q a) < ⊤ :=
  (isCompact_unipotentBox F q a).measure_lt_top

/-- The principal-level first row fits exactly the choice A = q + a. -/
theorem principalLevel_firstRow (q : ℤ) (a : ℕ)
    {y : Langlands.GeneralLinear (n + 1) F}
    (hy : y ∈ principalLevelSubgroup F n a) (j : Fin (n + 1)) (hj : j ≠ 0) :
    y.val 0 j ∈ 𝓛 (q - (q + a)) := by
  have h := ((mem_principalLevelSubgroup_iff y).1 hy).1 0 j
  rw [Matrix.one_apply_ne hj.symm, sub_zero, levelSet_eq_additiveLattice F] at h
  simpa using h

/-- The small transvection belongs to the same principal subgroup as its scalar. -/
theorem cutoffUnipotent_mem_principalLevel (m : ℕ) {a : ℕ} (ha : 0 < a)
    {x : F} (hx : x ∈ levelSet F a) :
    rankOneCutoffUnipotent m x ∈ principalLevelSubgroup F (m + 1) a := by
  obtain ⟨y, hy, he⟩ := exists_mem_principalLevelSubgroup (m := m + 1) ha
    (rankOneCutoffUnipotent m x).val (by
      intro i j
      rw [rankOneCutoffUnipotent_apply, Matrix.one_apply, add_sub_cancel_left]
      split_ifs
      · exact hx
      · exact zero_mem_levelSet a)
  rwa [show y = rankOneCutoffUnipotent m x from Units.ext he] at hy

/-- Right principal-level invariance gives a support bound independent of H. -/
theorem rankOne_support_of_principalLevel (ψ : UnitaryAdditiveCharacter F)
    {m : ℕ} {a : ℕ} (ha : 0 < a)
    (H : Langlands.GeneralLinear (m + 1 + 1) F → ℂ)
    (heq : ∀ u : upperUnipotent (m + 1 + 1) F, ∀ h,
      H (u.val * h) = (standardCharacter ψ (m + 1) u : ℂ) * H h)
    (hstab : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ h, H (h * y) = H h)
    (g : Langlands.GeneralLinear (0 + 1) F) (hg : H (rankOneEmbedding m g) ≠ 0) :
    ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ∈
      𝓛 ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a) := by
  rw [← sub_neg_eq_add]
  apply (⟨⟩ : LocalFieldData F).mem_additiveLattice_of_forall_mul_eq_one ψ (-(a : ℤ))
  intro x hx
  have hx' : x ∈ levelSet F a := by rwa [levelSet_eq_additiveLattice F]
  have h := hstab _ (cutoffUnipotent_mem_principalLevel F m ha hx') (rankOneEmbedding m g)
  rw [rankOneEmbedding_mul_cutoffUnipotent] at h
  rw [heq ⟨_, rankOneCutoffUnipotent_mem m _⟩,
    standardCharacter_rankOneCutoffUnipotent] at h
  have hψ : ψ.complex (((Matrix.GeneralLinearGroup.det g : Fˣ) : F) * x) = 1 :=
    (mul_eq_right₀ hg).1 h
  rw [UnitaryAdditiveCharacter.complex_apply] at hψ
  exact Subtype.ext hψ

/-- Right invariance of the box coefficient uses only the inequality q ≤ A. -/
theorem boxCoefficient_mul_principalLevel {A q : ℤ} {a : ℕ} (hqA : q ≤ A)
    (hL : ∀ y ∈ principalLevelSubgroup F n a,
      ∀ j, j ≠ 0 → y.val 0 j ∈ 𝓛 (q - A))
    (H : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hstab : ∀ y ∈ principalLevelSubgroup F n a, ∀ h, H (h * y) = H h)
    (h : Langlands.GeneralLinear (n + 1) F)
    {y : Langlands.GeneralLinear (n + 1) F}
    (hy : y ∈ principalLevelSubgroup F n a) :
    boxLatticeTest F A q a (h * y).val * H (h * y) =
      boxLatticeTest F A q a h.val * H h := by
  rw [hstab y hy, boxLatticeTest_apply, boxLatticeTest_apply, Units.val_mul]
  have hb := mul_mem_box_iff_of_le F hqA hL h.val hy
  by_cases hh : h.val ∈ box F A q a
  · rw [Set.indicator_of_mem (hb.2 hh), Set.indicator_of_mem hh]
  · rw [Set.indicator_of_notMem (fun h' => hh (hb.1 h')), Set.indicator_of_notMem hh]

/-- Pointwise extraction applies to an arbitrary left-equivariant coefficient,
without a representation or a selected vector. -/
theorem boxCoefficient_point (ψ : UnitaryAdditiveCharacter F)
    {m : ℕ} {A q : ℤ} {a : ℕ} (ha : 0 < a) (hqA : q ≤ A)
    (hL : ∀ y ∈ principalLevelSubgroup F (m + 1) a,
      ∀ j, j ≠ 0 → y.val 0 j ∈ 𝓛 (q - A))
    (hψ : ∀ z ∈ 𝓛 q, ψ z = 1)
    (hlev : ∀ z ∈ levelSet F a, z ∈ 𝓛 q)
    (H : Langlands.GeneralLinear (m + 1 + 1) F → ℂ)
    (heq : ∀ u : upperUnipotent (m + 1 + 1) F, ∀ h,
      H (u.val * h) = (standardCharacter ψ (m + 1) u : ℂ) * H h)
    (hstab : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ h, H (h * y) = H h)
    (hsupp : ∀ g : Langlands.GeneralLinear (0 + 1) F,
      H (rankOneEmbedding m g) ≠ 0 →
        ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ∈ 𝓛 A)
    (g : Langlands.GeneralLinear (0 + 1) F) (t : Fin (m + 1) → Fˣ)
    (u : upperUnipotent (m + 1 + 1) F) :
    boxLatticeTest F A q a (point ((g, t), u)).val * H (point ((g, t), u)) =
      (H (rankOneEmbedding m g) *
        (torusBox F a).indicator (fun _ => (1 : ℂ)) t) *
        (unipotentBox F q a).indicator (fun _ => (1 : ℂ)) u := by
  rw [boxLatticeTest_apply]
  by_cases ht : t ∈ torusBox F a
  · have hδ := torusFactor_mem F ha ht
    have hbox : (point ((g, t), u)).val ∈ box F A q a ↔
        ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ∈ 𝓛 A ∧
          u ∈ unipotentBox F q a := by
      rw [point_eq_mul F g t u, Units.val_mul,
        mul_mem_box_iff_of_le F hqA hL _ hδ, mem_box_unipotent_mul_iff]
    have hH : H (point ((g, t), u)) =
        (standardCharacter ψ (m + 1) u : ℂ) * H (rankOneEmbedding m g) := by
      rw [point_eq_mul F g t u, hstab _ hδ]
      exact heq u (rankOneEmbedding m g)
    rw [Set.indicator_of_mem ht, mul_one, hH]
    by_cases hu : u ∈ unipotentBox F q a
    · rw [Set.indicator_of_mem hu, mul_one,
        standardCharacter_eq_one F ψ hψ hlev hu, one_mul]
      by_cases hg : ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ∈ 𝓛 A
      · rw [Set.indicator_of_mem (hbox.2 ⟨hg, hu⟩), one_mul]
      · rw [Set.indicator_of_notMem (fun h => hg (hbox.1 h).1), zero_mul]
        have h0 : H (rankOneEmbedding m g) = 0 := by
          by_contra h
          exact hg (hsupp g h)
        exact h0.symm
    · rw [Set.indicator_of_notMem (fun h => hu (hbox.1 h).2),
        Set.indicator_of_notMem hu]
      simp
  · rw [Set.indicator_of_notMem (fun h => ht (mem_torusBox_of_mem_box F h)),
      Set.indicator_of_notMem ht]
    simp

/-- The positive extraction constant depends only on the box and its rank. -/
def boxExtractionConstant (A q : ℤ) (a : ℕ) : ℝ :=
  boxComparisonVolume F n A q a

theorem boxExtractionConstant_pos {A q : ℤ} {a : ℕ} (hA : 0 ≤ A) (ha : 0 < a) :
    0 < boxExtractionConstant F (n := n) A q a := by
  refine mul_pos ?_ (mul_pos ?_ ?_)
  · exact ENNReal.toReal_pos (restrict_boxSupport_pos F hA).ne'
      (restrict_boxSupport_lt_top F A q a).ne
  · exact ENNReal.toReal_pos (tailMeasure_torusBox_pos F ha _).ne'
      (tailMeasure_torusBox_lt_top F ha _).ne
  · exact ENNReal.toReal_pos (unipotentHaar_unipotentBox_pos F q a).ne'
      (unipotentHaar_unipotentBox_lt_top_all F q a).ne

/-- One fixed box extracts every continuous, equivariant, principal-level
invariant coefficient, with equivalence of genuine absolute convergence. -/
theorem boxCoefficient_extraction_of_principalLevel
    (ψ : UnitaryAdditiveCharacter F) {m : ℕ}
    {A q : ℤ} {a : ℕ} (ha : 0 < a) (hA : 0 ≤ A) (hqA : q ≤ A)
    (hL : ∀ y ∈ principalLevelSubgroup F (m + 1) a,
      ∀ j, j ≠ 0 → y.val 0 j ∈ 𝓛 (q - A))
    (hψ : ∀ z ∈ 𝓛 q, ψ z = 1)
    (hlev : ∀ z ∈ levelSet F a, z ∈ 𝓛 q)
    (H : Langlands.GeneralLinear (m + 1 + 1) F → ℂ) (hH : Continuous H)
    (heq : ∀ u : upperUnipotent (m + 1 + 1) F, ∀ h,
      H (u.val * h) = (standardCharacter ψ (m + 1) u : ℂ) * H h)
    (hstab : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ h, H (h * y) = H h)
    (hsupp : ∀ g : Langlands.GeneralLinear (0 + 1) F,
      H (rankOneEmbedding m g) ≠ 0 →
        ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ∈ 𝓛 A) :
    (Integrable (fun h => boxLatticeTest F A q a h.val * H h)
        (generalLinearHaar F (m + 1)) ↔
      Integrable (fun g => H (rankOneEmbedding m g)) (glOneMeasure F (m + 1))) ∧
    ∫ h, boxLatticeTest F A q a h.val * H h ∂generalLinearHaar F (m + 1) =
      (boxExtractionConstant F (n := m + 1) A q a : ℂ) *
        ∫ g, H (rankOneEmbedding m g) ∂glOneMeasure F (m + 1) := by
  let B : Langlands.GeneralLinear (m + 1 + 1) F → ℂ :=
    fun h => boxLatticeTest F A q a h.val * H h
  let G : Langlands.GeneralLinear (0 + 1) F → ℂ :=
    fun g => H (rankOneEmbedding m g)
  have hBc : Continuous B :=
    (((boxLatticeTest F A q a).locallyConstant.continuous.comp Units.continuous_val).mul hH)
  have hGc : Continuous G := hH.comp (continuous_rankOneEmbedding F m)
  have hSm : MeasurableSet (boxSupport F (n := m + 1) A q a) :=
    (isOpen_boxSupport F A q a).measurableSet
  have hTm : MeasurableSet (torusBox F (n := m + 1) a) :=
    (isOpen_torusBox F ha _).measurableSet
  have hUm : MeasurableSet (unipotentBox F (n := m + 1) q a) :=
    (isOpen_unipotentBox F q a).measurableSet
  have hin : ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer (m + 1),
      k ∈ boxSupport F A q a →
      ∃ r : (Langlands.GeneralLinear (0 + 1) F × (Fin (m + 1) → Fˣ)) ×
          upperUnipotent (m + 1 + 1) F →
        (Langlands.GeneralLinear (0 + 1) F × (Fin (m + 1) → Fˣ)) ×
          upperUnipotent (m + 1 + 1) F,
        MeasurePreserving r (iwasawaMeasure F (m + 1)) (iwasawaMeasure F (m + 1)) ∧
          ∀ x, B (point x * k) = B (point (r x)) := by
    rintro k hk ⟨-, x₀, hx₀⟩
    obtain ⟨xβ, hβ, y, hy, rfl⟩ := exists_point_mul_of_mem_box F ha hk hx₀
    refine ⟨rshift xβ, measurePreserving_rshift F _ xβ hβ, fun x => ?_⟩
    change boxLatticeTest F A q a _ * H _ = _
    rw [← mul_assoc, boxCoefficient_mul_principalLevel F hqA hL H hstab _ hy, point_rshift]
  have hout : ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer (m + 1),
      k ∉ boxSupport F A q a → ∀ x, B (point x * k) = 0 := by
    intro k hk hkS x
    have hnot : (point x * k).val ∉ box F A q a := fun h => hkS ⟨hk, x, h⟩
    simp only [B, boxLatticeTest_apply, Set.indicator_of_notMem hnot, zero_mul]
  have hpoint : ∀ x, B (point x) =
      (G x.1.1 * (torusBox F a).indicator (fun _ => (1 : ℂ)) x.1.2) *
        (unipotentBox F q a).indicator (fun _ => (1 : ℂ)) x.2 := by
    rintro ⟨⟨g, t⟩, u⟩
    exact boxCoefficient_point F ψ ha hqA hL hψ hlev H heq hstab hsupp g t u
  have hnorm : ∫⁻ h, ‖B h‖ₑ ∂generalLinearHaar F (m + 1) =
      (generalLinearHaar F (m + 1)).restrict
          (integralSubgroup (ValuativeRel.valuation F).integer (m + 1) :
            Set (Langlands.GeneralLinear (m + 1 + 1) F)) (boxSupport F A q a) *
        ((∫⁻ g, ‖G g‖ₑ ∂glOneMeasure F (m + 1)) *
          (tailMeasure F (m + 1) (torusBox F a) *
            unipotentHaar F (m + 1) (unipotentBox F q a))) := by
    rw [lintegral_enorm_eq_of_support F B hBc _ hSm hin hout,
      lintegral_param_of_eq F B G _ _ hTm hUm hpoint hGc.measurable]
  have hiff : Integrable B (generalLinearHaar F (m + 1)) ↔
      Integrable G (glOneMeasure F (m + 1)) := by
    constructor
    · intro hb
      refine ⟨hGc.aestronglyMeasurable, ?_⟩
      change ∫⁻ g, ‖G g‖ₑ ∂glOneMeasure F (m + 1) < ⊤
      by_contra hlt
      have htop : ∫⁻ g, ‖G g‖ₑ ∂glOneMeasure F (m + 1) = ⊤ :=
        top_unique (le_of_not_gt hlt)
      have hfin := hb.2
      change ∫⁻ h, ‖B h‖ₑ ∂generalLinearHaar F (m + 1) < ⊤ at hfin
      rw [hnorm, htop] at hfin
      simp [(restrict_boxSupport_pos F (n := m + 1) (q := q) (a := a) hA).ne',
        (tailMeasure_torusBox_pos F ha (m + 1)).ne',
        (unipotentHaar_unipotentBox_pos F (n := m + 1) q a).ne'] at hfin
    · intro hg
      refine ⟨hBc.aestronglyMeasurable, ?_⟩
      change ∫⁻ h, ‖B h‖ₑ ∂generalLinearHaar F (m + 1) < ⊤
      rw [hnorm]
      exact ENNReal.mul_lt_top (restrict_boxSupport_lt_top F A q a)
        (ENNReal.mul_lt_top hg.2 (ENNReal.mul_lt_top (tailMeasure_torusBox_lt_top F ha _)
          (unipotentHaar_unipotentBox_lt_top_all F q a)))
  refine ⟨hiff, ?_⟩
  by_cases hb : Integrable B (generalLinearHaar F (m + 1))
  · change ∫ h, B h ∂generalLinearHaar F (m + 1) = _
    rw [integral_eq_of_support F B hBc _ hSm hin hout hb,
      integral_param_of_eq F B G _ _ hTm hUm hpoint, Complex.real_smul]
    simp only [boxExtractionConstant, boxComparisonVolume]
    push_cast
    ring
  · have hg : ¬ Integrable G (glOneMeasure F (m + 1)) := fun h => hb (hiff.2 h)
    change ∫ h, B h ∂generalLinearHaar F (m + 1) =
      _ * ∫ g, G g ∂glOneMeasure F (m + 1)
    rw [integral_undef hb, integral_undef hg, mul_zero]

/-- At additive conductor c, the single box with A = c + a and q = c works
uniformly for every coefficient fixed by the same positive principal level. -/
theorem uniform_box_extraction (ψ : UnitaryAdditiveCharacter F)
    {m : ℕ} {a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ (⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
    (H : Langlands.GeneralLinear (m + 1 + 1) F → ℂ) (hH : Continuous H)
    (heq : ∀ u : upperUnipotent (m + 1 + 1) F, ∀ h,
      H (u.val * h) = (standardCharacter ψ (m + 1) u : ℂ) * H h)
    (hstab : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ h, H (h * y) = H h) :
    let c := (⟨⟩ : LocalFieldData F).additiveConductor ψ
    (Integrable (fun h => boxLatticeTest F (c + a) c a h.val * H h)
        (generalLinearHaar F (m + 1)) ↔
      Integrable (fun g => H (rankOneEmbedding m g)) (glOneMeasure F (m + 1))) ∧
    ∫ h, boxLatticeTest F (c + a) c a h.val * H h ∂generalLinearHaar F (m + 1) =
      (boxExtractionConstant F (n := m + 1) (c + a) c a : ℂ) *
        ∫ g, H (rankOneEmbedding m g) ∂glOneMeasure F (m + 1) := by
  apply boxCoefficient_extraction_of_principalLevel F ψ ha hA (by omega)
    (fun _ hy => principalLevel_firstRow F _ a hy)
    ((⟨⟩ : LocalFieldData F).additiveTrivialAt_iff_le_conductor ψ _ |>.2 le_rfl)
    (fun z hz => ?_) H hH heq hstab
    (rankOne_support_of_principalLevel F ψ ha H heq hstab)
  rw [levelSet_eq_additiveLattice F] at hz
  exact lattice_mono F (by omega) hz

end Langlands.AllField.RankinSelberg.RankOneBox
