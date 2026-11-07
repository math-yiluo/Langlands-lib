import Langlands.Representation.Classification.Segments
import Mathlib.Order.Interval.Finset.Fin

/-! The half-modulus cancellation for a consecutive rank-one segment. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators NNReal

namespace Langlands

private theorem pairRatioProduct {M : Type*} [CommGroup M] (m : ℕ) (x : Fin m → M) :
    (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), x i / x j) =
      (∏ i, x i ^ (m - 1 - i.val)) / (∏ i, x i ^ i.val) := by
  simp_rw [Finset.prod_div_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Finset.prod_const]
    congr 1
    have h : Finset.univ.filter (fun j : Fin m => i < j) = Finset.Ioi i := by
      ext j
      simp
    rw [h, Fin.card_Ioi]
  · simp_rw [Finset.prod_filter]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j _
    rw [← Finset.prod_filter, Finset.prod_const]
    congr 1
    have h : Finset.univ.filter (fun i : Fin m => i < j) = Finset.Iio j := by
      ext i
      simp
    rw [h, Fin.card_Iio]

private theorem pairRatioHalfProduct (m : ℕ) (x : Fin m → ℝ≥0ˣ) :
    NNReal.sqrt
        ((∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), x i / x j : ℝ≥0ˣ) :
          ℝ≥0) *
      (∏ i, (x i : ℝ≥0) ^ (i.val : ℝ)) =
        (∏ i, (x i : ℝ≥0)) ^ (((m : ℝ) - 1) / 2) := by
  rw [pairRatioProduct]
  simp only [Units.val_div_eq_div_val, Units.coe_prod, Units.val_pow_eq_pow_val]
  rw [NNReal.sqrt_eq_rpow, NNReal.div_rpow]
  simp_rw [← NNReal.finsetProd_rpow, ← NNReal.rpow_natCast_mul]
  rw [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← NNReal.rpow_sub (x i).ne_zero, ← NNReal.rpow_add (x i).ne_zero]
  congr 1
  have hi : i.val ≤ m - 1 := by omega
  rw [Nat.cast_sub hi]
  have hm : 1 ≤ m := by omega
  rw [Nat.cast_sub hm]
  push_cast
  ring

namespace PadicField.TopologicalData

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The determinant character at the midpoint of a rank-one segment. -/
def rankOneSegmentCharacter (m : ℕ) (χ : F.Carrierˣ →* ℂˣ) :
    GeneralLinear (m * 1) F.Carrier →* ℂˣ :=
  T.determinantPowerCharacter (m * 1) (((m : ℝ) - 1) / 2) *
    χ.comp GeneralLinear.determinant

/-- The positive half-modulus cancels the varying twists in an increasing
rank-one string, leaving the uniform midpoint exponent. -/
theorem leviHalfModulus_uniform_one (m : ℕ)
    (l : (GeneralLinear.BlockShape.uniform m 1 (by omega)).Levi F.Carrier) :
    T.leviHalfModulus (GeneralLinear.BlockShape.uniform m 1 (by omega)) l *
        ∏ i : Fin m, realPowerCharacter (T.determinantNorm 1) (i.val : ℝ) (l i) =
      ∏ i : Fin m,
        realPowerCharacter (T.determinantNorm 1) (((m : ℝ) - 1) / 2) (l i) := by
  apply Units.ext
  simp only [Units.val_mul, Units.coe_prod, leviHalfModulus_apply,
    coe_realPowerCharacter]
  have h := pairRatioHalfProduct m (fun i => T.determinantNorm 1 (l i))
  have hmod :
      T.leviModulus (GeneralLinear.BlockShape.uniform m 1 (by omega)) l =
        ∏ i, ∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
          T.determinantNorm 1 (l i) / T.determinantNorm 1 (l j) := by
    have hfull :=
      T.leviModulus_apply (GeneralLinear.BlockShape.uniform m 1 (by omega)) l
    change T.leviModulus (GeneralLinear.BlockShape.uniform m 1 (by omega)) l =
      ∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j),
        T.determinantNorm 1 (l i) ^ 1 / T.determinantNorm 1 (l j) ^ 1 at hfull
    simpa only [pow_one] using hfull
  rw [hmod]
  rw [← NNReal.finsetProd_rpow] at h
  simpa only [Units.coe_prod, coe_realPowerCharacter, NNReal.coe_mul, NNReal.coe_prod,
    NNReal.coe_rpow, Complex.ofReal_mul, Complex.ofReal_prod] using
      congrArg (fun x : ℝ≥0 => ((x : ℝ) : ℂ)) h

end PadicField.TopologicalData
end Langlands
