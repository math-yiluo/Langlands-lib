import Langlands.Representation.GodementJacquet.CentralMatrixRationality
import Langlands.AllField.Representation.GodementJacquet.CompactMatrixLaurent
/-! # Rational continuation from compact scalar covers -/

noncomputable section

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding MatrixConverges centralMatrixRationalityBorelSpace centralMatrixRationalityLocalField centralMatrixRationalityMeasurableSpace centralMatrixRationalityT2Space centralMatrixRationalityTopology centralMatrixRationalityValuativeRel compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel determinantWeight_shift_spectral exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_laurent_matrixIntegral_quotient exists_shiftedRationalValue_of_scalarSaturation instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instTopologicalSpaceCarrier instValuativeRelCarrier jpssI2 jpssI3 laurentEval_matrixGeometricDenominator matrixGeometricDenominator matrixGeometricDenominator_ne_zero matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding MatrixConverges jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance centralMatrixRationalityT2Space : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance centralMatrixRationalityMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance centralMatrixRationalityBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}

/-- The common central geometric denominator, in the exact shifted spectral variable. -/
def matrixGeometricDenominator (z : Langlands.GeneralLinear (n + 1) F)
    (ω : ℂ) : LaurentCoefficients :=
  1 - LaurentPolynomial.C
    (ω * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) z (jpssShift n)) *
      LaurentPolynomial.T ((⟨⟩ : LocalFieldData F).ord (Matrix.det z.val))

/-- Spectral evaluation gives precisely the analytic recurrence denominator. -/
theorem laurentEval_matrixGeometricDenominator
    (z : Langlands.GeneralLinear (n + 1) F) (ω s : ℂ) :
    laurentEval (spectralUnit (Nat.zero_lt_one.trans
      (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s)
      (matrixGeometricDenominator F z ω) =
      1 - ω * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        z (s + jpssShift n) := by
  rw [matrixGeometricDenominator, map_sub, map_one, map_mul, laurentEval_C,
    laurentEval_T, coe_spectralUnit, determinantWeight_shift_spectral]
  ring

/-- The compact central difference has an everywhere convergent Laurent value;
the original integral is its geometric quotient wherever the ratio contracts. -/
theorem exists_laurent_matrixIntegral_quotient
    (z : Langlands.GeneralLinear (n + 1) F)
    (hz : normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det z.val) < 1)
    (ω : ℂ) (Φ : MatrixTestFunction n F)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) (hf : Continuous f)
    (hcov : ∀ g, f (z * g) = ω * f g)
    (K : Set (Langlands.GeneralLinear (n + 1) F)) (hK : IsCompact K)
    (hs : Function.support f ⊆ scalarSaturation K) :
    ∃ A : LaurentCoefficients, ∀ s : ℂ,
      ‖ω * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        z (s + jpssShift n)‖ < 1 →
      MatrixConverges F Φ (s + jpssShift n) f ∧
        matrixIntegral F Φ (s + jpssShift n) f =
          laurentEval (spectralUnit (Nat.zero_lt_one.trans
            (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s) A /
            (1 - ω * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
              z (s + jpssShift n)) := by
  obtain ⟨A, hA⟩ := exists_laurent_matrixIntegral_of_hasCompactSupport F
    (matrixTestDifference z Φ) f hf
    (hasCompactSupport_matrixTestDifference_mul z Φ f K hK hs)
  refine ⟨A, fun s hr => ?_⟩
  obtain ⟨hi, he⟩ := matrixIntegral_eq_div_of_difference
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (⟨⟩ : LocalFieldData F).continuous_normalizedAbs
    (generalLinearHaar F n) z hz ω f hf hcov Φ (s + jpssShift n) hr (hA s).1
  exact ⟨hi, he.trans (congrArg (fun x => x /
    (1 - ω * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      z (s + jpssShift n))) (hA s).2)⟩

/-- The common geometric denominator is nonzero for every determinant contraction. -/
theorem matrixGeometricDenominator_ne_zero
    (z : Langlands.GeneralLinear (n + 1) F)
    (hz : normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det z.val) < 1)
    (ω : ℂ) : matrixGeometricDenominator F z ω ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_halfPlane_norm_matrixRatio_lt_one
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) z hz ω (jpssShift n)
  intro he
  have hn := ha (a + 1) (by simp)
  have hev := laurentEval_matrixGeometricDenominator F z ω (a + 1)
  rw [he, map_zero] at hev
  have hratio := (sub_eq_zero.mp hev.symm).symm
  rw [hratio, norm_one] at hn
  exact (lt_irrefl _ hn)

/-- Actual shifted rational continuation, with one common Laurent denominator
and an explicit numerator clearing identity. -/
theorem exists_shiftedRationalValue_of_scalarSaturation
    (z : Langlands.GeneralLinear (n + 1) F)
    (hz : normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det z.val) < 1)
    (ω : ℂ) (Φ : MatrixTestFunction n F)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) (hf : Continuous f)
    (hcov : ∀ g, f (z * g) = ω * f g)
    (K : Set (Langlands.GeneralLinear (n + 1) F)) (hK : IsCompact K)
    (hs : Function.support f ⊆ scalarSaturation K) :
    ∃ R : RationalFunctions,
      HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (generalLinearHaar F n) Φ f R ∧
      ∃ A : LaurentCoefficients,
        laurentToRatFunc A = laurentToRatFunc (matrixGeometricDenominator F z ω) * R := by
  obtain ⟨A, hA⟩ := exists_laurent_matrixIntegral_quotient F z hz ω Φ f hf hcov K hK hs
  obtain ⟨a, ha⟩ := exists_halfPlane_norm_matrixRatio_lt_one
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) z hz ω (jpssShift n)
  let D := matrixGeometricDenominator F z ω
  let R := laurentToRatFunc A / laurentToRatFunc D
  have hD : laurentToRatFunc D ≠ 0 :=
    (map_ne_zero_iff laurentToRatFunc laurentToRatFunc_injective).mpr
      (matrixGeometricDenominator_ne_zero F z hz ω)
  refine ⟨R, ⟨⟨a, fun s hs => (hA s (ha s hs)).1⟩, a, fun s hs => ?_⟩,
    A, ?_⟩
  · let x := spectralUnit (Nat.zero_lt_one.trans
      (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s
    have hratio : 1 - ω * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        z (s + jpssShift n) ≠ 0 := by
      intro he
      have hh := ha s hs
      rw [← sub_eq_zero.mp he, norm_one] at hh
      exact lt_irrefl _ hh
    have hDe : RatFunc.eval (RingHom.id ℂ) (x : ℂ) (laurentToRatFunc D) =
        1 - ω * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          z (s + jpssShift n) :=
      (eval_laurentToRatFunc x D).trans (laurentEval_matrixGeometricDenominator F z ω s)
    have hDe0 : RatFunc.eval (RingHom.id ℂ) (x : ℂ) (laurentToRatFunc D) ≠ 0 := by
      rw [hDe]
      exact hratio
    have hreg : RationalEvaluation.RegularAt R (x : ℂ) := by
      simpa only [R, div_eq_mul_inv] using
        RationalEvaluation.RegularAt.mul (laurentToRatFunc_regular x A)
        (RationalEvaluation.RegularAt.inv hDe0)
    refine ⟨hreg, (hA s (ha s hs)).2.trans ?_⟩
    symm
    change RatFunc.eval (RingHom.id ℂ) (x : ℂ)
      (laurentToRatFunc A / laurentToRatFunc D) = laurentEval x A / _
    rw [RationalEvaluation.eval_div (laurentToRatFunc_regular x A) hDe0,
      hDe, eval_laurentToRatFunc x A]
  · exact (mul_div_cancel₀ (laurentToRatFunc A) hD).symm.trans (by rw [mul_comm])

end Langlands.AllField.GodementJacquet.Padic
