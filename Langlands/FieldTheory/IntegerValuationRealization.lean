import Mathlib.Data.Int.WithZero
import Langlands.ClassFieldTheory.Local.SeparableInertiaNormAmbient

/-! # Real realization of an integer-valued valuation -/

noncomputable section

open scoped NNReal WithZero

namespace Langlands.FieldTheory

open Langlands.ClassFieldTheory.Local.SeparableInertiaNorm

variable {K : Type*} [Field K]

/-- Real realization with exponential base two. -/
def integerValuationToReal (v : Valuation K ℤᵐ⁰) : Valuation K ℝ≥0 :=
  v.map (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0))
    (WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2)).monotone

@[simp] theorem integerValuationToReal_apply (v : Valuation K ℤᵐ⁰) (x : K) :
    integerValuationToReal v x =
      WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v x) := rfl

/-- The realization keeps the actual valuation subring. -/
@[simp] theorem integerValuationToReal_valuationSubring (v : Valuation K ℤᵐ⁰) :
    (integerValuationToReal v).valuationSubring = v.valuationSubring := by
  apply ValuationSubring.ext
  intro x
  change WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v x) ≤ 1 ↔ v x ≤ 1
  exact WithZeroMulInt.toNNReal_le_one_iff (by norm_num : (1 : ℝ≥0) < 2)

/-- Henselianity is preserved because the subring is unchanged. -/
theorem integerValuationToReal_valHensel (v : Valuation K ℤᵐ⁰)
    [HenselianLocalRing v.valuationSubring] : ValHensel (integerValuationToReal v) := by
  have : HenselianLocalRing (integerValuationToReal v).valuationSubring := by
    rw [integerValuationToReal_valuationSubring]
    infer_instance
  exact valHensel_of_henselian _

/-- Algebraically closed residue fields give the required residue-root property. -/
theorem integerValuationToReal_valResidueRoot (v : Valuation K ℤᵐ⁰)
    [IsAlgClosed (IsLocalRing.ResidueField v.valuationSubring)] :
    ValResidueRoot (integerValuationToReal v) := by
  have : IsAlgClosed (IsLocalRing.ResidueField
      (integerValuationToReal v).valuationSubring) := by
    rw [integerValuationToReal_valuationSubring]
    infer_instance
  exact valResidueRoot_of_isAlgClosed _

/-- A preimage of `exp (-1)` is a uniformizer in real coordinates. -/
theorem integerValuationToReal_uniformizer (v : Valuation K ℤᵐ⁰) {π : K}
    (hπ : v π = WithZero.exp (-1 : ℤ)) :
    ValUniformizer (integerValuationToReal v) π := by
  refine ⟨?_, ?_, fun b hb0 hb1 => ?_⟩
  · change 0 < WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v π)
    rw [hπ]
    exact WithZeroMulInt.toNNReal_pos _ WithZero.exp_ne_zero
  · change WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v π) < 1
    rw [hπ, WithZeroMulInt.toNNReal_lt_one_iff (by norm_num : (1 : ℝ≥0) < 2)]
    simp
  · have hv0 : v b ≠ 0 := v.ne_zero_iff.mpr hb0
    have hv1 : v b ≤ 1 :=
      (WithZeroMulInt.toNNReal_le_one_iff (by norm_num : (1 : ℝ≥0) < 2)).mp hb1
    have hn : WithZero.log (v b) ≤ 0 := by
      rwa [WithZero.log_le_iff_le_exp hv0, WithZero.exp_zero]
    refine ⟨(-WithZero.log (v b)).toNat, ?_⟩
    have hval : v b = v π ^ (-WithZero.log (v b)).toNat := by
      rw [hπ, ← WithZero.exp_nsmul, nsmul_eq_mul]
      have he : ((-WithZero.log (v b)).toNat : ℤ) * (-1) = WithZero.log (v b) := by
        rw [Int.toNat_of_nonneg (by omega)]
        ring
      rw [he, WithZero.exp_log hv0]
    change WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v b) =
      WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v π) ^ _
    simpa only [map_pow] using congrArg
      (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)) hval

/-- Surjectivity supplies a uniformizer without an additional DVR assumption. -/
theorem integerValuationToReal_exists_uniformizer (v : Valuation K ℤᵐ⁰)
    (hv : Function.Surjective v) :
    ∃ π : K, ValUniformizer (integerValuationToReal v) π := by
  obtain ⟨π, hπ⟩ := hv (WithZero.exp (-1 : ℤ))
  exact ⟨π, integerValuationToReal_uniformizer v hπ⟩

end Langlands.FieldTheory
