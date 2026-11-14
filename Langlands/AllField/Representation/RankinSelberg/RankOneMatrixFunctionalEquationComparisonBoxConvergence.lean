import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxConvergence
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxCoefficient
/-! # Actual rank-one convergence from matrix analytic data

A deep box and a compact averaging subgroup preserve the actual model function
on the box. Tonelli's exact positive norm identity then transfers convergence
from the matrix coefficient to the rank-one integral.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg.RankOneBox hiding ModelBoxConditions averagedModelCoefficient_eq_of_left_invariant box boxCoefficientBorelSpace boxCoefficientLocalField boxCoefficientMeasurableSpace boxCoefficientTopology boxCoefficientValuativeRel boxConvergenceBorelSpace boxConvergenceLocalField boxConvergenceMeasurableSpace boxConvergenceSecondCountable boxConvergenceT2 boxConvergenceTopology boxConvergenceUnipotentBorel boxConvergenceUnipotentMeasurable boxConvergenceUnitsBorel boxConvergenceUnitsMeasurable boxConvergenceUnitsSecondCountable boxConvergenceValuativeRel boxEntry boxSupport box_comparison_of_integrable box_eq_pi box_matrixIntegrand_eq_of_eq_on_box coe_unitLevel continuous_determinantWeight continuous_glModelFunction continuous_rankOneEmbedding continuous_unipotent_entry determinantRankOne_point diagonalUnits_mem_principalLevel exists_box_averagedModelCoefficient_eq exists_box_constant exists_mem_principalLevel_mul_inv_upper exists_point_mul_of_mem_box glLocallyCompact glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integer_of_mem_principalLevel integral_eq_of_support integral_param_of_eq inv_sub_one_mem_levelSet isCompact_box isCompact_boxEntry isOpen_box isOpen_boxEntry isOpen_boxSupport isOpen_torusBox isOpen_unipotentBox isOpen_unitLevel lintegral_enorm_eq_of_support lintegral_param_of_eq matrixIntegrand_mul_principalLevel matrixIntegrand_point matrixLocallyCompact measurableSet_integralSubgroup measurePreserving_rshift mem_box_iff mem_box_unipotent_mul_iff mem_torusBox_of_mem_box mem_unitLevel_iff modelFunction_eq_determinantRankOne_of_mem_box mul_mem_box mul_mem_box_iff mul_sub_one_mem_levelSet one_mem_box one_mem_boxSupport one_mem_unipotentBox parameterBase_isMulLeftInvariant point_eq_mul principalLevel_le_integral rankOneEmbedding_eq_point rankOneModelValues_subset rankOneModel_convergesOnRight_of_matrix restrict_boxSupport_lt_top restrict_boxSupport_pos standardCharacter_eq_one tailMeasure_torusBox tailMeasure_torusBox_lt_top tailMeasure_torusBox_pos torusBox torusBox_eq_pi torusFactor_mem unipotentBox unipotentBox_subset unipotentHaar_unipotentBox_lt_top unipotentHaar_unipotentBox_pos unipotentLocallyCompact unipotentSecondCountable unipotent_mul_rankOne_apply unipotent_mul_rankOne_apply_zero unitLevel unitLevel_le_integralUnits unitLevel_measure_le unitLevel_measure_pos unitsSecondCountable weight_smul_integrand
open Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneModelValues_subset_whittakerRationalValues singleton_modulus_real zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker
open Langlands.Conductor
open Langlands.RankinSelberg.RankOneIwasawa hiding ColBound colBound_of_inv colBound_zero congruenceGroup congruenceGroup_le_integral conj_mem_congruenceGroup continuous_det_units continuous_point continuous_torusCoord continuous_torusModulus continuous_weight det_point elemUnipotent elemUnipotent_val exists_congruenceGroup_le exists_cornerSchwartz exists_lattice_nontrivial exists_lattice_subset exists_mem_lattice exists_mem_matLattice exists_ne_zero_of_unipotentTransform_ne_zero exists_schwartz_congruence glLocallyCompact glOneMeasure glOneMeasure_sigmaFinite glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instIsNonarchimedeanLocalFieldCarrier_3 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instTopologicalSpaceCarrier_3 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 instValuativeRelCarrier_3 integralSubgroup_mem_matLattice integral_mul_matLattice inv_mem_lattice_of_notMem inv_mem_of_colBound isCompact_lattice isOpen_congruenceGroup isOpen_lattice isOpen_matLattice iwasawaMeasure iwasawaMeasure_point_preimage iwasawaMeasure_sFinite lattice_mono lattice_mul map_iwasawaMeasure_prod map_unfoldedMeasure matLattice matLattice_basis matLattice_mono matLattice_mul matLattice_mul_integral matrixLocallyCompact measurable_point measurable_unfoldedPoint measurePreserving_shift mem_lattice_zero_iff mem_matLattice mem_matLattice_of_support mul_sub_one_mem one_add_mem_lattice_zero one_add_single_apply one_mem_lattice_zero parameterBase_isMulLeftInvariant parameterMeasure parameterMeasure_eq_prod parameterMeasure_sigmaFinite schwartzOfLattice schwartzOfLattice_apply schwartz_invariance schwartz_support_bound standardCharacter_elemUnipotent tailMeasure tailMeasure_sigmaFinite torusModulus torusModulus_apply torusModulus_cons_one torusModulus_eq_one unfoldedMeasure unfoldedPoint unipotentConj_map unipotentLocallyCompact unipotentSecondCountable unipotentTransform unipotentTransform_diag_bounds unipotentTransform_eq_zero_of_shift unipotentTransform_mul_right unipotent_col_zero unipotent_mul_single_zero unitsSecondCountable weight weight_apply weight_glOne weight_split
open Langlands.AllField.RankinSelberg.RankOneIwasawa
open Langlands.RankinSelberg.UnequalRankMirabolicUnitTest
open scoped NNReal ENNReal

universe uF uV

section Convergence

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance boxConvergenceT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance boxConvergenceMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance boxConvergenceBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

local instance boxConvergenceUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance boxConvergenceUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance boxConvergenceSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance boxConvergenceUnitsSecondCountable : SecondCountableTopology Fˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance boxConvergenceUnitsMeasurable : MeasurableSpace Fˣ := borel _
local instance boxConvergenceUnitsBorel : BorelSpace Fˣ := ⟨rfl⟩

local notation "𝓛" => (Langlands.LocalFieldData.additiveLattice (⟨⟩ : LocalFieldData F))

variable (ψ : UnitaryAdditiveCharacter F) {m : ℕ} {V : Type uV}
  [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V)
  (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)

/-- The explicit hypotheses needed by the rank-one box integral calculation. -/
def ModelBoxConditions (A q : ℤ) (a : ℕ) : Prop :=
  0 < a ∧ 0 ≤ A ∧ q ≤ 0 ∧
    (∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ j, j ≠ 0 →
      y.val 0 j ∈ 𝓛 (q - A)) ∧
    (∀ z ∈ 𝓛 q, ψ z = 1) ∧
    (∀ z ∈ levelSet F a, z ∈ 𝓛 q) ∧
    (∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g) ∧
    (∀ g : Langlands.GeneralLinear (0 + 1) F,
      glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) ≠ 0 →
        ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ∈ 𝓛 A)

/-- A compact averaging subgroup can be chosen so that its actual coefficient
agrees pointwise with the model function on a box satisfying all integral hypotheses. -/
theorem exists_box_averagedModelCoefficient_eq (hσ : IsSmooth σ) :
    ∃ (A q : ℤ) (a : ℕ), ModelBoxConditions F ψ σ ℓ w A q a ∧
      ∃ K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F),
        ∃ hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F)),
          (∀ k ∈ K,
            (∀ M, (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
                (isOpen_box F A q a)) (k.val * M) =
              (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
                (isOpen_box F A q a)) M) ∧
              normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det k.val) = 1) ∧
          ∀ g : Langlands.GeneralLinear (m + 1 + 1) F,
            g.val ∈ box F A q a →
              (Langlands.AllField.GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w).val g =
                glModelFunction ψ (m + 1) σ ℓ w g := by
  obtain ⟨A₀, hA₀⟩ := exists_rankOneEmbedding_support (⟨⟩ : LocalFieldData F) ψ σ hσ ℓ w
  have hA : 0 ≤ max A₀ 0 := le_max_right _ _
  have hsupp : ∀ g : Langlands.GeneralLinear (0 + 1) F,
      glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) ≠ 0 →
        ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ∈ 𝓛 (max A₀ 0) :=
    fun g h => lattice_mono F (le_max_left _ _) (hA₀ g h)
  have hq : min ((⟨⟩ : LocalFieldData F).additiveConductor ψ) 0 ≤ 0 := min_le_right _ _
  have hψ : ∀ z ∈ 𝓛 (min ((⟨⟩ : LocalFieldData F).additiveConductor ψ) 0), ψ z = 1 :=
    ((⟨⟩ : LocalFieldData F).additiveTrivialAt_iff_le_conductor ψ _).2 (min_le_left _ _)
  set A : ℤ := max A₀ 0 with hAdef
  set q : ℤ := min ((⟨⟩ : LocalFieldData F).additiveConductor ψ) 0 with hqdef
  obtain ⟨Kw, hKw⟩ := glModel_isSmooth ψ (m + 1) σ hσ ℓ w
  have hrow : IsOpen {g : Langlands.GeneralLinear (m + 1 + 1) F |
      ∀ j, j ≠ 0 → g.val 0 j ∈ 𝓛 (q - A)} := by
    have h : {g : Langlands.GeneralLinear (m + 1 + 1) F |
        ∀ j, j ≠ 0 → g.val 0 j ∈ 𝓛 (q - A)} =
        ⋂ j, ⋂ (_ : j ≠ 0), (fun g : Langlands.GeneralLinear (m + 1 + 1) F =>
          g.val 0 j) ⁻¹' (𝓛 (q - A) : Set F) := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rw [h]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
      (isOpen_lattice F _).preimage (Units.continuous_val.matrix_elem 0 j)
  let KD := Kw.comap (determinantRankOne (m + 1)) (continuous_determinantRankOne (m + 1))
  have hU : ((Kw ⊓ KD : OpenSubgroup _) : Set (Langlands.GeneralLinear (m + 1 + 1) F)) ∩
      {g | ∀ j, j ≠ 0 → g.val 0 j ∈ 𝓛 (q - A)} ∈
        𝓝 (1 : Langlands.GeneralLinear (m + 1 + 1) F) := by
    refine Filter.inter_mem ((Kw ⊓ KD).isOpen.mem_nhds (one_mem _)) (hrow.mem_nhds fun j hj => ?_)
    change (1 : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) F) 0 j ∈ 𝓛 (q - A)
    rw [Matrix.one_apply_ne (Ne.symm hj)]
    exact zero_mem _
  obtain ⟨a, ha, haU⟩ := exists_pos_principalLevelOpenSubgroup_subset F (m + 1) hU
  have hmemU : ∀ y ∈ principalLevelSubgroup F (m + 1) a,
      y ∈ ((Kw ⊓ KD : OpenSubgroup _) : Set (Langlands.GeneralLinear (m + 1 + 1) F)) ∩
        {g | ∀ j, j ≠ 0 → g.val 0 j ∈ 𝓛 (q - A)} := fun y hy => haU hy
  have hL : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ j, j ≠ 0 →
      y.val 0 j ∈ 𝓛 (q - A) := fun y hy => (hmemU y hy).2
  have hstab : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g := by
    intro y hy g
    have hfix : glModelRepresentation ψ (m + 1) σ ℓ y w = w := hKw ⟨y, (hmemU y hy).1.1⟩
    rw [← glModelFunction_translate, hfix]
  have hlev : ∀ z ∈ levelSet F a, z ∈ 𝓛 q := by
    intro z hz
    obtain ⟨E, hE, hEv⟩ := exists_mem_principalLevelSubgroup ha
      (1 + Matrix.single (0 : Fin (m + 1 + 1)) (Fin.succ 0) z) (by
        intro i l
        rw [Matrix.add_apply, add_sub_cancel_left, Matrix.single_apply]
        split_ifs
        · exact hz
        · exact zero_mem_levelSet a)
    have h := hL E hE (Fin.succ 0) (Fin.succ_ne_zero 0)
    have he : E.val 0 (Fin.succ 0) = z := by
      rw [hEv, Matrix.add_apply, Matrix.one_apply_ne (Fin.succ_ne_zero 0).symm,
        Matrix.single_apply_same, zero_add]
    rw [he] at h
    exact lattice_mono F (by omega) h
  have hDstab : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * determinantRankOne (m + 1) y) =
        glModelFunction ψ (m + 1) σ ℓ w g := by
    intro y hy g
    have hfix : glModelRepresentation ψ (m + 1) σ ℓ (determinantRankOne (m + 1) y) w = w :=
      hKw ⟨determinantRankOne (m + 1) y, (hmemU y hy).1.2⟩
    rw [← glModelFunction_translate, hfix]
  let Φ : GodementJacquet.MatrixTestFunction (m + 1) F := compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a)
  obtain ⟨K₀, hK₀, hΦ⟩ := Langlands.AllField.GodementJacquet.Padic.exists_compactOpen_matrixTest_invariant F Φ
  obtain ⟨K, hK, hsub⟩ := (⟨⟩ : LocalFieldData F).generalLinearCompactOpen (m + 1 + 1)
    (((K₀ ⊓ KD : OpenSubgroup _) : Set _)) ((K₀ ⊓ KD).isOpen.mem_nhds (one_mem _))
  refine ⟨A, q, a, ⟨ha, hA, hq, hL, hψ, hlev, hstab, hsupp⟩, K, hK,
    (fun k hk => hΦ k (hsub hk).1), ?_⟩
  intro g hg
  apply averagedModelCoefficient_eq_of_left_invariant F ψ σ ℓ w hσ K hK g
  intro k hk
  have hkg : (k * g).val ∈ box F A q a := by
    have h := (hΦ k (hsub hk).1).1 g.val
    change (box F A q a).indicator (fun _ => (1 : ℂ)) (k.val * g.val) =
      (box F A q a).indicator (fun _ => (1 : ℂ)) g.val at h
    rw [Set.indicator_of_mem hg] at h
    by_contra hn
    change k.val * g.val ∉ box F A q a at hn
    rw [Set.indicator_of_notMem hn] at h
    exact zero_ne_one h
  rw [modelFunction_eq_determinantRankOne_of_mem_box F ψ σ ℓ w ha hA hq hL hψ hlev
      hstab hDstab hkg,
    modelFunction_eq_determinantRankOne_of_mem_box F ψ σ ℓ w ha hA hq hL hψ hlev
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

/-- The same box comparison runs in reverse: absolute matrix convergence
implies absolute rank-one convergence, and the integral has its exact positive factor. -/
theorem box_comparison_of_integrable (hσ : IsSmooth σ) {A q : ℤ} {a : ℕ}
    (hbox : ModelBoxConditions F ψ σ ℓ w A q a) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      Integrable (GodementJacquet.matrixIntegrand
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a))
          (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w))
        (generalLinearHaar F (m + 1)) →
      Integrable (rankOneModelIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          σ ℓ w s) (generalLinearHaar F 0) ∧
      (∫ g, GodementJacquet.matrixIntegrand
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a))
          (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w) g
          ∂generalLinearHaar F (m + 1)) =
        (C : ℂ) * ∫ g, rankOneModelIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          σ ℓ w s g ∂generalLinearHaar F 0 := by
  rcases hbox with ⟨ha, hA, hq, hL, hψ, hlev, hstab, hsupp⟩
  have hSm : MeasurableSet (boxSupport F (n := m + 1) A q a) :=
    (isOpen_boxSupport F A q a).measurableSet
  have hTm : MeasurableSet (torusBox F (n := m + 1) a) := (isOpen_torusBox F ha _).measurableSet
  have hUm : MeasurableSet (unipotentBox F (n := m + 1) q a) :=
    (isOpen_unipotentBox F q a).measurableSet
  have hC : 0 < ((generalLinearHaar F (m + 1)).restrict
      (integralSubgroup (ValuativeRel.valuation F).integer (m + 1) :
        Set (Langlands.GeneralLinear (m + 1 + 1) F))).real (boxSupport F A q a) *
      ((tailMeasure F (m + 1)).real (torusBox F a) *
        (unipotentHaar F (m + 1)).real (unipotentBox F q a)) := by
    refine mul_pos ?_ (mul_pos ?_ ?_)
    · exact ENNReal.toReal_pos (restrict_boxSupport_pos F hA).ne'
        (restrict_boxSupport_lt_top F A q a).ne
    · exact ENNReal.toReal_pos (tailMeasure_torusBox_pos F ha _).ne'
        (tailMeasure_torusBox_lt_top F ha _).ne
    · exact ENNReal.toReal_pos (unipotentHaar_unipotentBox_pos F q a).ne'
        (unipotentHaar_unipotentBox_lt_top F hq a).ne
  refine ⟨_, hC, fun s hHint => ?_⟩
  set H := GodementJacquet.matrixIntegrand (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a))
    (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w) with hH
  set Fg : Langlands.GeneralLinear (0 + 1) F → ℂ := fun g =>
    glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) *
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
        (s + GodementJacquet.jpssShift (m + 1)) with hFg_def
  have hHc : Continuous H :=
    (((compactOpenIndicator (box F A q a) (isCompact_box F A q a)
      (isOpen_box F A q a)).locallyConstant.continuous.comp Units.continuous_val).mul
        (continuous_glModelFunction F ψ σ hσ ℓ w)).mul (continuous_determinantWeight F _ _)
  have hFgc : Continuous Fg :=
    ((continuous_glModelFunction F ψ σ hσ ℓ w).comp (continuous_rankOneEmbedding F m)).mul
      (continuous_determinantWeight F _ _)
  have hin : ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer (m + 1),
      k ∈ boxSupport F A q a →
      ∃ r : (Langlands.GeneralLinear (0 + 1) F × (Fin (m + 1) → Fˣ)) ×
          upperUnipotent (m + 1 + 1) F →
        (Langlands.GeneralLinear (0 + 1) F × (Fin (m + 1) → Fˣ)) ×
          upperUnipotent (m + 1 + 1) F,
        MeasurePreserving r (iwasawaMeasure F (m + 1)) (iwasawaMeasure F (m + 1)) ∧
          ∀ x, H (point x * k) = H (point (r x)) := by
    rintro k hk ⟨-, x₀, hx₀⟩
    obtain ⟨xβ, hβ, y, hy, rfl⟩ := exists_point_mul_of_mem_box F ha hk hx₀
    refine ⟨rshift xβ, measurePreserving_rshift F _ xβ hβ, fun x => ?_⟩
    rw [← mul_assoc, hH, matrixIntegrand_mul_principalLevel F ψ σ ℓ w hA hq hL hstab _ _ hy,
      point_rshift]
  have hout : ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer (m + 1),
      k ∉ boxSupport F A q a → ∀ x, H (point x * k) = 0 := by
    intro k hk hkS x
    have hnot : (point x * k).val ∉ box F A q a := fun h => hkS ⟨hk, x, h⟩
    simp only [hH, GodementJacquet.matrixIntegrand, coe_compactOpenIndicator,
      Set.indicator_of_notMem hnot, zero_mul]
  have hpoint : ∀ x, H (point x) =
      (Fg x.1.1 * (torusBox F a).indicator (fun _ => (1 : ℂ)) x.1.2) *
        (unipotentBox F q a).indicator (fun _ => (1 : ℂ)) x.2 := by
    rintro ⟨⟨g, t⟩, u⟩
    exact matrixIntegrand_point F ψ σ ℓ w ha hA hq hL hψ hlev hstab hsupp _ g t u
  have hwm : Measurable fun g : Langlands.GeneralLinear (0 + 1) F =>
      weight F (m + 1) (g, 1) :=
    ((continuous_weight F (m + 1)).comp (continuous_id.prodMk continuous_const)).measurable
  have hglOne_l : ∫⁻ g, ‖Fg g‖ₑ ∂glOneMeasure F (m + 1) =
      ∫⁻ g, ‖rankOneModelIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        σ ℓ w s g‖ₑ ∂generalLinearHaar F 0 := by
    have hwm' : Measurable fun g : Langlands.GeneralLinear (0 + 1) F =>
        ((weight F (m + 1) (g, 1) : ℝ≥0) : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hwm
    rw [glOneMeasure, lintegral_withDensity_eq_lintegral_mul _ hwm' hFgc.measurable.enorm]
    refine lintegral_congr fun g => ?_
    rw [Pi.mul_apply, ← weight_smul_integrand F ψ σ ℓ w s g, NNReal.smul_def, enorm_smul,
      NNReal.enorm_eq]
  have hglOne_i : ∫ g, Fg g ∂glOneMeasure F (m + 1) =
      ∫ g, rankOneModelIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        σ ℓ w s g ∂generalLinearHaar F 0 := by
    rw [glOneMeasure, integral_withDensity_eq_integral_smul hwm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
      weight_smul_integrand F ψ σ ℓ w s g)
  have hnorm : ∫⁻ g, ‖H g‖ₑ ∂generalLinearHaar F (m + 1) =
      (generalLinearHaar F (m + 1)).restrict
        (integralSubgroup (ValuativeRel.valuation F).integer (m + 1) :
          Set (Langlands.GeneralLinear (m + 1 + 1) F)) (boxSupport F A q a) *
      ((∫⁻ g, ‖rankOneModelIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          σ ℓ w s g‖ₑ ∂generalLinearHaar F 0) *
        (tailMeasure F (m + 1) (torusBox F a) *
          unipotentHaar F (m + 1) (unipotentBox F q a))) := by
    rw [lintegral_enorm_eq_of_support F H hHc _ hSm hin hout,
      lintegral_param_of_eq F H Fg _ _ hTm hUm hpoint hFgc.measurable, hglOne_l]
  have hfin : ∫⁻ g, ‖rankOneModelIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      σ ℓ w s g‖ₑ ∂generalLinearHaar F 0 < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hm := hHint.2
    change ∫⁻ g, ‖H g‖ₑ ∂generalLinearHaar F (m + 1) < ⊤ at hm
    rw [hnorm, htop] at hm
    simp [(restrict_boxSupport_pos F hA).ne',
      (tailMeasure_torusBox_pos F ha (m + 1)).ne',
      (unipotentHaar_unipotentBox_pos F q a).ne'] at hm
  have hrankc : Continuous (rankOneModelIntegrand ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) σ ℓ w s) :=
    ((continuous_glModelFunction F ψ σ hσ ℓ w).comp (continuous_rankOneEmbedding F m)).mul
      (continuous_determinantWeight F _ _)
  refine ⟨⟨hrankc.aestronglyMeasurable, hfin⟩, ?_⟩
  rw [integral_eq_of_support F H hHc _ hSm hin hout hHint,
    integral_param_of_eq F H Fg _ _ hTm hUm hpoint, hglOne_i, Complex.real_smul]
  push_cast
  ring

/-- Agreement on the box is enough for equality of the complete matrix integrands. -/
theorem box_matrixIntegrand_eq_of_eq_on_box {A q : ℤ} {a : ℕ}
    {f₁ f₂ : Langlands.GeneralLinear (m + 1 + 1) F → ℂ}
    (heq : ∀ g, g.val ∈ box F A q a → f₁ g = f₂ g) (s : ℂ) :
    GodementJacquet.matrixIntegrand (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a)) s f₁ =
      GodementJacquet.matrixIntegrand (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a)) s f₂ := by
  funext g
  by_cases hg : g.val ∈ box F A q a
  · simp only [GodementJacquet.matrixIntegrand, coe_compactOpenIndicator,
      Set.indicator_of_mem hg, heq g hg]
  · simp only [GodementJacquet.matrixIntegrand, coe_compactOpenIndicator,
      Set.indicator_of_notMem hg, zero_mul]

/-- A common matrix half-plane for the actual coefficient model gives a common
right half-plane for every actual rank-one model integral. -/
theorem rankOneModel_convergesOnRight_of_matrix (hσ : IsSmooth σ)
    (hMatrix : Langlands.AllField.GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ)) :
    ∃ b : ℝ, ∀ w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
      ∀ s : ℂ, b < s.re →
        Integrable (rankOneModelIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          σ ℓ w s) (generalLinearHaar F 0) := by
  obtain ⟨b, hb⟩ := hMatrix
  refine ⟨b, fun w s hs => ?_⟩
  obtain ⟨A, q, a, hbox, K, hK, -, heq⟩ :=
    exists_box_averagedModelCoefficient_eq F ψ σ ℓ w hσ
  obtain ⟨C, -, hcomp⟩ := box_comparison_of_integrable F ψ σ ℓ w hσ hbox
  apply (hcomp s ?_).1
  have hm := hb (compactOpenIndicator (box F A q a) (isCompact_box F A q a)
    (isOpen_box F A q a)) (Langlands.AllField.GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w) s hs
  change Integrable _ _ at hm
  rwa [box_matrixIntegrand_eq_of_eq_on_box F heq] at hm

end Convergence

end Langlands.AllField.RankinSelberg.RankOneBox
