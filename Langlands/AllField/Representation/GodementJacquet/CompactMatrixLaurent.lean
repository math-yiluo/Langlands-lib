import Langlands.Representation.GodementJacquet.CompactMatrixLaurent
import Langlands.AllField.Representation.GodementJacquet.Zeta
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement
/-! # Laurent integrals of compactly supported matrix functions -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open scoped BigOperators

universe uX uF

section DiscreteWeight



end DiscreteWeight

namespace Padic
open Langlands.GodementJacquet.Padic hiding MatrixConverges compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel determinantWeight_shift_spectral exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instTopologicalSpaceCarrier instValuativeRelCarrier jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding MatrixConverges jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance compactMatrixLaurentMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
  borel _
local instance compactMatrixLaurentBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}

/-- The shifted determinant weight separates into a fixed weight and an
integer power of the exact spectral point. -/
theorem determinantWeight_shift_spectral (g : Langlands.GeneralLinear (n + 1) F)
    (s t : ℂ) :
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g (s + t) =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g t *
        spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^
          (⟨⟩ : LocalFieldData F).ord (Matrix.det g.val) := by
  rw [determinantWeight, Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr
      ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).pos g.det_ne_zero).ne')]
  rw [mul_comm]
  congr 1
  exact normalizedDeterminantWeight_eq_spectralPoint_zpow (⟨⟩ : LocalFieldData F) g s

/-- Every compactly supported continuous group function has an everywhere
convergent determinant Mellin transform with a Laurent polynomial value. -/
theorem exists_laurent_integral_of_hasCompactSupport
    (h : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hh : Continuous h) (hc : HasCompactSupport h) (t : ℂ) :
    ∃ A : LaurentCoefficients, ∀ s : ℂ,
      Integrable (fun g => h g *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g (s + t))
          (generalLinearHaar F n) ∧
      (∫ g, h g *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g (s + t)
          ∂generalLinearHaar F n) =
        laurentEval
          (spectralUnit (Nat.zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s)
          A := by
  let T := (⟨⟩ : LocalFieldData F)
  let ord : Langlands.GeneralLinear (n + 1) F → ℤ :=
    fun g => T.ord (Matrix.det g.val)
  have hord : Continuous ord :=
    (continuous_ord_units T).comp (T.generalLinearDeterminant (n + 1)).continuous
  have hw : Continuous (fun g : Langlands.GeneralLinear (n + 1) F =>
      determinantWeight (normalizedAbsoluteValue T) g t) := by
    simp_rw [normalizedDeterminantWeight_eq_spectralPoint_zpow T]
    exact (continuous_of_discreteTopology : Continuous
      (fun m : ℤ => spectralPoint T.residueCardinality t ^ m)).comp hord
  obtain ⟨A, hA⟩ := exists_laurent_integral_discreteWeight
    (generalLinearHaar F n) T.residueCardinality
    (Nat.zero_lt_one.trans T.residueCardinality_gt_one) ord hord
    (fun g => h g * determinantWeight (normalizedAbsoluteValue T) g t)
    (hh.mul hw) hc.mul_right
  refine ⟨A, fun s => ?_⟩
  simpa only [determinantWeight_shift_spectral, mul_assoc, ord] using hA s

/-- Compactness of the test times coefficient on the group gives an exact
Laurent value and absolute convergence at every shifted parameter. -/
theorem exists_laurent_matrixIntegral_of_hasCompactSupport
    (Φ : MatrixTestFunction n F)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport (fun g => Φ g.val * f g)) :
    ∃ A : LaurentCoefficients, ∀ s : ℂ,
      MatrixConverges F Φ (s + jpssShift n) f ∧
      matrixIntegral F Φ (s + jpssShift n) f =
        laurentEval
          (spectralUnit (Nat.zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s)
          A := by
  exact exists_laurent_integral_of_hasCompactSupport F (fun g => Φ g.val * f g)
    ((Φ.continuous.comp Units.continuous_val).mul hf) hc (jpssShift n)

end Padic

end Langlands.AllField.GodementJacquet
