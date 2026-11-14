import Langlands.Representation.GodementJacquet.MatrixDenominatorCancellation
import Langlands.AllField.Representation.GodementJacquet.CentralMatrixRationality
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement
/-! # Cancellation of the actual central matrix denominators -/

noncomputable section

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding MatrixConverges centralMatrixRationalityBorelSpace centralMatrixRationalityLocalField centralMatrixRationalityMeasurableSpace centralMatrixRationalityT2Space centralMatrixRationalityTopology centralMatrixRationalityValuativeRel compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel determinantWeight_shift_spectral exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_laurent_matrixIntegral_quotient exists_laurent_of_matrix_geometric_clearings exists_shiftedRationalValue_of_scalarSaturation instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instTopologicalSpaceCarrier instValuativeRelCarrier jpssI2 jpssI3 laurentEval_matrixGeometricDenominator matrixGeometricCoefficient matrixGeometricCoefficient_reflected_product matrixGeometricCoefficient_reflected_product_ne_one matrixGeometricDenominator matrixGeometricDenominator_ne_zero matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding MatrixConverges jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.LocalFactor

universe uF

variable (F : Type uF) [Field F]

variable {n : ℕ}

/-- The scalar coefficient in the shifted central geometric denominator. -/
def matrixGeometricCoefficient [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (z : Langlands.GeneralLinear (n + 1) F) (ω : ℂ) : ℂ :=
  ω * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) z (jpssShift n)

/-- The coefficient product of the original and reflected dual denominators
is the positive determinant norm raised to the matrix rank. -/
theorem matrixGeometricCoefficient_reflected_product [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (z : Langlands.GeneralLinear (n + 1) F) (ω : ℂˣ) :
    matrixGeometricCoefficient F z ω *
        (matrixGeometricCoefficient F z (ω⁻¹ : ℂˣ) *
          (spectralReflectionUnit (Nat.zero_lt_one.trans
            (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) : ℂ) ^
              (⟨⟩ : LocalFieldData F).ord (Matrix.det z.val)) =
      ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (Matrix.det z.val) : ℂ) ^
        (n + 1) := by
  let a := (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (Matrix.det z.val)
  have ha : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).pos z.det_ne_zero).ne'
  have hsp : spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality (1 : ℂ) =
      ((⟨⟩ : LocalFieldData F).residueCardinality : ℂ)⁻¹ := by
    simp only [spectralPoint, Complex.cpow_neg_one]
  have hω : (ω : ℂ) * ((ω⁻¹ : ℂˣ) : ℂ) = 1 := by
    exact_mod_cast ω.mul_inv
  unfold matrixGeometricCoefficient
  rw [coe_spectralReflectionUnit]
  calc
    _ = determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          z (jpssShift n) *
        (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          z (jpssShift n) *
            ((⟨⟩ : LocalFieldData F).residueCardinality : ℂ)⁻¹ ^
              (⟨⟩ : LocalFieldData F).ord (Matrix.det z.val)) := by
      calc
        _ = ((ω : ℂ) * ((ω⁻¹ : ℂˣ) : ℂ)) *
          (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            z (jpssShift n) *
            (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
              z (jpssShift n) *
              ((⟨⟩ : LocalFieldData F).residueCardinality : ℂ)⁻¹ ^
                (⟨⟩ : LocalFieldData F).ord (Matrix.det z.val))) := by ring
        _ = _ := by rw [hω, one_mul]
    _ = determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          z (jpssShift n) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          z (1 + jpssShift n) := by
      rw [determinantWeight_shift_spectral, hsp]
    _ = (a : ℂ) ^ (jpssShift n + (1 + jpssShift n)) := by
      exact (Complex.cpow_add _ _ ha).symm
    _ = (a : ℂ) ^ ((n + 1 : ℕ) : ℂ) := by
      congr 1
      simp only [jpssShift, Nat.cast_add, Nat.cast_one]
      ring
    _ = (a : ℂ) ^ (n + 1) := by rw [Complex.cpow_natCast]

/-- Determinant contraction makes the reflected coefficient product different
from one, independently of the central character. -/
theorem matrixGeometricCoefficient_reflected_product_ne_one [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (z : Langlands.GeneralLinear (n + 1) F)
    (hz : normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det z.val) < 1)
    (ω : ℂˣ) :
    matrixGeometricCoefficient F z ω *
        (matrixGeometricCoefficient F z (ω⁻¹ : ℂˣ) *
          (spectralReflectionUnit (Nat.zero_lt_one.trans
            (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) : ℂ) ^
              (⟨⟩ : LocalFieldData F).ord (Matrix.det z.val)) ≠ 1 := by
  rw [matrixGeometricCoefficient_reflected_product]
  have hlt := pow_lt_one₀
    ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).nonneg (Matrix.det z.val))
    hz (Nat.succ_ne_zero n)
  intro he
  have hr : normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det z.val) ^
      (n + 1) = 1 := by exact_mod_cast he
  exact (ne_of_lt hlt) hr

/-- An actual monomial functional equation and the two central geometric
clearings force the original rational function to be Laurent. -/
theorem exists_laurent_of_matrix_geometric_clearings [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (z : Langlands.GeneralLinear (n + 1) F)
    (hz : normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det z.val) < 1)
    (ω c : ℂˣ) (m : ℤ) {R RDual : RationalFunctions}
    (hD : ∃ A : LaurentCoefficients, laurentToRatFunc A =
      laurentToRatFunc (matrixGeometricDenominator F z ω) * R)
    (hE : ∃ B : LaurentCoefficients, laurentToRatFunc B =
      laurentToRatFunc (matrixGeometricDenominator F z (ω⁻¹ : ℂˣ)) * RDual)
    (hFE : NormalizedFunctionalEquation (⟨⟩ : LocalFieldData F).residueCardinality
      1 1 1 c 0 m R RDual) :
    ∃ A : LaurentCoefficients, laurentToRatFunc A = R := by
  exact exists_laurent_of_reflected_geometric_clearings
    (spectralReflectionUnit (Nat.zero_lt_one.trans
      (⟨⟩ : LocalFieldData F).residueCardinality_gt_one))
    (matrixGeometricCoefficient F z ω)
    (matrixGeometricCoefficient F z (ω⁻¹ : ℂˣ))
    ((⟨⟩ : LocalFieldData F).ord (Matrix.det z.val))
    (matrixGeometricCoefficient_reflected_product_ne_one F z hz ω)
    (laurentMonomialUnit c m) hD hE
    (hFE.rational_identity (⟨⟩ : LocalFieldData F).residueCardinality_gt_one)

end Langlands.AllField.GodementJacquet.Padic
