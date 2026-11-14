import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxFourier
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonLatticeFourier
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox
/-! The actual Fourier transform of the rank-one comparison box. -/

noncomputable section

open MeasureTheory
open scoped BigOperators WithZero

namespace Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg.RankOneBox hiding box boxEntry boxLatticeCentre boxLatticeTest boxLatticeTest_apply boxLatticeTest_eq_compactOpenIndicator boxSupport box_eq_pi box_eq_rectangularLatticeCoset coe_unitLevel continuous_determinantWeight continuous_glModelFunction continuous_rankOneEmbedding continuous_unipotent_entry diagonalUnits_mem_principalLevel exists_box_constant exists_mem_principalLevel_mul_inv_upper exists_point_mul_of_mem_box glLocallyCompact glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integer_of_mem_principalLevel integral_eq_of_support integral_param_of_eq inv_sub_one_mem_levelSet isCompact_box isCompact_boxEntry isOpen_box isOpen_boxEntry isOpen_boxSupport isOpen_torusBox isOpen_unipotentBox isOpen_unitLevel levelSet_eq_additiveLattice lintegral_enorm_eq_of_support lintegral_param_of_eq matrixIntegrand_mul_principalLevel matrixIntegrand_point matrixLocallyCompact measurableSet_integralSubgroup measurePreserving_rshift mem_box_iff mem_box_unipotent_mul_iff mem_torusBox_of_mem_box mem_unitLevel_iff mul_mem_box mul_mem_box_iff mul_sub_one_mem_levelSet one_mem_box one_mem_boxSupport one_mem_unipotentBox parameterBase_isMulLeftInvariant point_eq_mul principalLevel_le_integral rankOneEmbedding_eq_point rankOneModelValues_subset restrict_boxSupport_lt_top restrict_boxSupport_pos standardCharacter_eq_one tailMeasure_torusBox tailMeasure_torusBox_lt_top tailMeasure_torusBox_pos torusBox torusBox_eq_pi torusFactor_mem unipotentBox unipotentBox_subset unipotentHaar_unipotentBox_lt_top unipotentHaar_unipotentBox_pos unipotentLocallyCompact unipotentSecondCountable unipotent_mul_rankOne_apply unipotent_mul_rankOne_apply_zero unitLevel unitLevel_le_integralUnits unitLevel_measure_le unitLevel_measure_pos unitsSecondCountable weight_smul_integrand
open Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneModelValues_subset_whittakerRationalValues singleton_modulus_real zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement isClopen_rectangularLatticeCoset isCompact_rectangularLatticeCoset mem_rectangularLatticeCoset padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists rectangularLatticeCoset rectangularLatticeCosetTest rectangularLatticeCosetTest_apply
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.UnequalRankMirabolicUnitTest

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2

local notation "T" => (⟨⟩ : LocalFieldData F)
local notation "𝓛" => (Langlands.LocalFieldData.additiveLattice (⟨⟩ : LocalFieldData F))

/-- The actual maximal-ideal power used by the published box is precisely the
negative-index valuation lattice. -/
theorem levelSet_eq_additiveLattice (a : ℕ) :
    levelSet F a = (𝓛 (-(a : ℤ)) : Set F) := by
  have hv : (⟨⟩ : LocalFieldData F).discreteValuation.Integers (⟨⟩ : LocalFieldData F).Integers := by
    refine ⟨Subtype.val_injective, ?_, ?_⟩
    · intro x
      exact ((⟨⟩ : LocalFieldData F).mem_integers_iff_discreteValuation_le_one x.val).1 x.property
    · intro x hx
      exact ⟨⟨x, ((⟨⟩ : LocalFieldData F).mem_integers_iff_discreteValuation_le_one x).2 hx⟩, rfl⟩
  let π : (⟨⟩ : LocalFieldData F).Integers := ⟨(⟨⟩ : LocalFieldData F).uniformizer,
    ((⟨⟩ : LocalFieldData F).mem_integers_iff_discreteValuation_le_one _).2 (by
      rw [(⟨⟩ : LocalFieldData F).discreteValuation_uniformizer]
      norm_num)⟩
  have hπ : (⟨⟩ : LocalFieldData F).discreteValuation (π : F) = WithZero.exp (-1) :=
    (⟨⟩ : LocalFieldData F).discreteValuation_uniformizer
  have hm : IsLocalRing.maximalIdeal (⟨⟩ : LocalFieldData F).Integers = Ideal.span {π} := by
    ext x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one,
      ← SetLike.mem_coe, hv.coe_span_singleton_eq_setOfPred_le_v_algebraMap]
    change (⟨⟩ : LocalFieldData F).discreteValuation x.val ≠ 1 ↔
      (⟨⟩ : LocalFieldData F).discreteValuation x.val ≤ (⟨⟩ : LocalFieldData F).discreteValuation (π : F)
    rw [hπ]
    have hle := hv.map_le_one x
    have hstep : (⟨⟩ : LocalFieldData F).discreteValuation x.val < 1 ↔
        (⟨⟩ : LocalFieldData F).discreteValuation x.val ≤ WithZero.exp (-1) := by
      simpa [← WithZero.exp_add] using
        (WithZero.lt_mul_exp_iff_le (x := (⟨⟩ : LocalFieldData F).discreteValuation x.val)
          (y := WithZero.exp (-1)) WithZero.exp_ne_zero)
    rw [← hstep]
    exact ⟨fun h => lt_of_le_of_ne hle h, fun h => h.ne⟩
  have hp : ((IsLocalRing.maximalIdeal (⟨⟩ : LocalFieldData F).Integers ^ a : Ideal (⟨⟩ : LocalFieldData F).Integers) :
      Set (⟨⟩ : LocalFieldData F).Integers) = {y : (⟨⟩ : LocalFieldData F).Integers | (⟨⟩ : LocalFieldData F).discreteValuation (y : F) ≤ WithZero.exp (-(a : ℤ))} := by
    rw [hm, Ideal.span_singleton_pow,
      hv.coe_span_singleton_eq_setOfPred_le_v_algebraMap]
    change {y : (⟨⟩ : LocalFieldData F).Integers | (⟨⟩ : LocalFieldData F).discreteValuation (y : F) ≤
      (⟨⟩ : LocalFieldData F).discreteValuation ((π : F) ^ a)} = _
    simp only [map_pow, hπ, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Set.ext_iff.1 hp y).1 hy
  · intro hx
    have hxO : x ∈ (⟨⟩ : LocalFieldData F).Integers :=
      ((⟨⟩ : LocalFieldData F).mem_additiveLattice_zero x).1 ((⟨⟩ : LocalFieldData F).additiveLattice_mono (by omega) hx)
    refine ⟨⟨x, hxO⟩, ?_, rfl⟩
    exact (Set.ext_iff.1 hp ⟨x, hxO⟩).2 hx

/-- The comparison box has centre zero in its first row and the identity in
all remaining rows. -/
def boxLatticeCentre (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  fun i j => if i = 0 then 0 else (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j

/-- Identification of the actual published box as an entrywise affine lattice
coset; this is an equality of subsets of the full matrix space. -/
theorem box_eq_rectangularLatticeCoset {n : ℕ} (A q : ℤ) (a : ℕ) :
    box F (n := n) A q a = rectangularLatticeCoset F T
      (boxLatticeLevels A q a) (boxLatticeCentre F n) := by
  ext X
  rw [mem_rectangularLatticeCoset]
  change (∀ i j, X i j ∈ boxEntry F A q a i j) ↔ _
  simp only [boxEntry, boxLatticeLevels, boxLatticeCentre, levelSet_eq_additiveLattice]
  constructor <;> intro h i j
  all_goals
    specialize h i j
    split_ifs at h ⊢ <;> simpa only [sub_zero, Set.mem_ofPred_eq, SetLike.mem_coe] using h

/-- The original comparison box test, expressed through its actual lattice
coset rather than through an unspecified Fourier partner. -/
def boxLatticeTest {n : ℕ} (A q : ℤ) (a : ℕ) :
    SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
  rectangularLatticeCosetTest F T (boxLatticeLevels A q a) (boxLatticeCentre F n)

@[simp] theorem boxLatticeTest_apply {n : ℕ} (A q : ℤ) (a : ℕ)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    boxLatticeTest F A q a X = (box F A q a).indicator (fun _ => (1 : ℂ)) X := by
  rw [boxLatticeTest, rectangularLatticeCosetTest_apply, ← box_eq_rectangularLatticeCoset]

/-- This is exactly the compact-open indicator in the existing box-integral
proof, as a Schwartz test on all matrices. -/
theorem boxLatticeTest_eq_compactOpenIndicator {n : ℕ} (A q : ℤ) (a : ℕ) :
    boxLatticeTest F (n := n) A q a =
      compactOpenIndicator (box F A q a) (isCompact_box F A q a) (isOpen_box F A q a) := by
  ext X
  rw [boxLatticeTest_apply, coe_compactOpenIndicator]

end Langlands.AllField.RankinSelberg.RankOneBox
