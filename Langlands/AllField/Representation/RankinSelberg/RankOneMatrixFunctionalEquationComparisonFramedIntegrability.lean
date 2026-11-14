import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFramedIntegrability
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox
/-! Compact support on unipotent times full matrices from an invertible frame. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
open Langlands.RankinSelberg.CompactWhittakerSynthesis hiding firstColumnFrame_mem_range_of_mem_box instValuativeRelCarrier_1
open Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneModelValues_subset_whittakerRationalValues singleton_modulus_real zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory MeasureTheory.Measure _root_.Topology
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear

universe uK uF

section General


end General

section FirstColumn


end FirstColumn

section CanonicalPadic

open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker
open Langlands.Conductor
open Langlands.RankinSelberg.UnequalRankMirabolicUnitTest

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- The first-column frame of every matrix in the actual comparison box is
invertible; the original matrix itself may be singular. -/
theorem firstColumnFrame_mem_range_of_mem_box (n : ℕ) (A q : ℤ) {a : ℕ}
    (ha : 0 < a)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hX : X ∈ Langlands.AllField.RankinSelberg.RankOneBox.box F A q a) :
    firstColumnFrame n X ∈ Set.range
      (Units.val : Langlands.GeneralLinear (n + 1) F →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F) := by
  let Y := (firstColumnFrame n X).updateRow 0
    ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) 0)
  have hY : ∀ i j, Y i j -
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j ∈
      levelSet F a := by
    intro i j
    by_cases hi : i = 0
    · subst i
      simp only [Y, Matrix.updateRow_self, sub_self]
      exact zero_mem_levelSet a
    · by_cases hj : j = 0
      · subst j
        simp only [Y, Matrix.updateRow_ne hi, firstColumnFrame, Matrix.updateCol_self,
          sub_self]
        exact zero_mem_levelSet a
      · simp only [Y, Matrix.updateRow_ne hi, firstColumnFrame, Matrix.updateCol_ne hj]
        exact ((Langlands.AllField.RankinSelberg.RankOneBox.mem_box_iff F X).mp hX).2.2 i hi j
  obtain ⟨y, _, hy⟩ := exists_mem_principalLevelSubgroup ha Y hY
  have hdet : (firstColumnFrame n X).det = y.val.det := by
    rw [hy, det_firstColumnFrame, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp [Y, firstColumnFrame, Matrix.updateRow_apply, Matrix.one_apply]
    congr 1
  exact ⟨((Matrix.isUnit_iff_isUnit_det (firstColumnFrame n X)).mpr
    (Ne.isUnit (hdet ▸ y.det_ne_zero))).unit, rfl⟩

end CanonicalPadic

end Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
