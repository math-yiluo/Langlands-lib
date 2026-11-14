import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxCoefficient
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonAveraging
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox
/-!
# Pointwise compact averaging on a rank-one matrix box

A sufficiently deep box identifies a model function with its value at the
rank-one diagonal of the determinant. A compact left averaging subgroup can
therefore be chosen to preserve the function pointwise on that box.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg.RankOneBox hiding averagedModelCoefficient_eq_of_left_invariant box boxCoefficientBorelSpace boxCoefficientLocalField boxCoefficientMeasurableSpace boxCoefficientTopology boxCoefficientValuativeRel boxEntry boxSupport box_eq_pi coe_unitLevel continuous_determinantWeight continuous_glModelFunction continuous_rankOneEmbedding continuous_unipotent_entry determinantRankOne_point diagonalUnits_mem_principalLevel exists_box_constant exists_mem_principalLevel_mul_inv_upper exists_point_mul_of_mem_box glLocallyCompact glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integer_of_mem_principalLevel integral_eq_of_support integral_param_of_eq inv_sub_one_mem_levelSet isCompact_box isCompact_boxEntry isOpen_box isOpen_boxEntry isOpen_boxSupport isOpen_torusBox isOpen_unipotentBox isOpen_unitLevel lintegral_enorm_eq_of_support lintegral_param_of_eq matrixIntegrand_mul_principalLevel matrixIntegrand_point matrixLocallyCompact measurableSet_integralSubgroup measurePreserving_rshift mem_box_iff mem_box_unipotent_mul_iff mem_torusBox_of_mem_box mem_unitLevel_iff modelFunction_eq_determinantRankOne_of_mem_box mul_mem_box mul_mem_box_iff mul_sub_one_mem_levelSet one_mem_box one_mem_boxSupport one_mem_unipotentBox parameterBase_isMulLeftInvariant point_eq_mul principalLevel_le_integral rankOneEmbedding_eq_point rankOneModelValues_subset restrict_boxSupport_lt_top restrict_boxSupport_pos standardCharacter_eq_one tailMeasure_torusBox tailMeasure_torusBox_lt_top tailMeasure_torusBox_pos torusBox torusBox_eq_pi torusFactor_mem unipotentBox unipotentBox_subset unipotentHaar_unipotentBox_lt_top unipotentHaar_unipotentBox_pos unipotentLocallyCompact unipotentSecondCountable unipotent_mul_rankOne_apply unipotent_mul_rankOne_apply_zero unitLevel unitLevel_le_integralUnits unitLevel_measure_le unitLevel_measure_pos unitsSecondCountable weight_smul_integrand
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

section Algebra

variable {E : Type*} [Field E]

@[simp]
theorem determinantRankOne_point (F : Type*) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {n : ℕ} (x : (Langlands.GeneralLinear (0 + 1) F × (Fin n → Fˣ)) ×
      upperUnipotent (n + 1) F) :
    determinantRankOne n (point x) =
      Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det x.1.1) 1) := by
  change Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det (point x)) 1) = _
  rw [det_point F]


end Algebra

section Pointwise

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance boxCoefficientMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance boxCoefficientBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

local notation "𝓛" => (Langlands.LocalFieldData.additiveLattice (⟨⟩ : LocalFieldData F))

variable (ψ : UnitaryAdditiveCharacter F) {m : ℕ} {V : Type uV}
  [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V)
  (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)

/-- On a deep box, a model function only depends on the determinant-rank-one diagonal. -/
theorem modelFunction_eq_determinantRankOne_of_mem_box {A q : ℤ} {a : ℕ}
    (ha : 0 < a) (hA : 0 ≤ A) (hq : q ≤ 0)
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
    exact (mul_mem_box_iff F hA hq hL g.val (inv_mem hy)).2 hg
  have ht := torusFactor_mem F ha (mem_torusBox_of_mem_box F hbox)
  have hu : u ∈ unipotentBox F q a := by
    have h := hbox
    rw [point_eq_mul F, Units.val_mul,
      mul_mem_box_iff F hA hq hL _ ht, mem_box_unipotent_mul_iff] at h
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

/-- Normalized averaging is pointwise the original function wherever every
left translate in the subgroup has the same value. -/
theorem averagedModelCoefficient_eq_of_left_invariant (hσ : IsSmooth σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F)))
    (g : Langlands.GeneralLinear (m + 1 + 1) F)
    (hinv : ∀ k ∈ K, glModelFunction ψ (m + 1) σ ℓ w (k * g) =
      glModelFunction ψ (m + 1) σ ℓ w g) :
    (Langlands.AllField.GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w).val g =
      glModelFunction ψ (m + 1) σ ℓ w g := by
  have hmass : ((generalLinearHaar F (m + 1)).real (K : Set _) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff]
    exact not_or.mpr ⟨(K.isOpen.measure_pos _ ⟨1, K.one_mem⟩).ne', hK.measure_lt_top.ne⟩
  rw [Langlands.AllField.GodementJacquet.Padic.averagedModelCoefficient_apply, GodementJacquet.normalizedLeftAverage]
  have heq : (∫ k in (K : Set _), glModelFunction ψ (m + 1) σ ℓ w (k * g)
      ∂generalLinearHaar F (m + 1)) =
      ∫ _ in (K : Set _), glModelFunction ψ (m + 1) σ ℓ w g
        ∂generalLinearHaar F (m + 1) := by
    apply setIntegral_congr_fun K.isOpen.measurableSet
    exact hinv
  rw [heq, setIntegral_const, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀ hmass, one_mul]

end Pointwise

end Langlands.AllField.RankinSelberg.RankOneBox
