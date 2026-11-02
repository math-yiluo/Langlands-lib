import Langlands.LocalField.LaurentSeries

/-! # The existing FML normalization on the X-adic Laurent-series field -/

open scoped WithZero

universe u

namespace Langlands.LocalField.Laurent

variable (k : Type u) [Field k] [Finite k]

attribute [local instance] valuativeRel

/-- The smallest positive value of the existing FML order occurs at `X`. -/
@[simp] theorem ord_single_one :
    FML.ord (LaurentSeries k) (HahnSeries.single (1 : ℤ) (1 : k)) = 1 := by
  have hpos : (0 : WithTop ℤ) <
      FML.ord (LaurentSeries k) (HahnSeries.single (1 : ℤ) (1 : k)) := by
    rw [← FML.ord_one (LaurentSeries k), FML.ord_lt_ord_iff]
    rw [(Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).vlt_iff_lt]
    simp [LaurentSeries.valuation_single_zpow]
  obtain ⟨π, _, hπ⟩ := FML.ord_surjective_nonzero (LaurentSeries k) 1
  have hπlt : (Valued.v π : ℤᵐ⁰) < 1 := by
    have h : FML.ord (LaurentSeries k) 1 < FML.ord (LaurentSeries k) π := by
      simp [hπ]
    have hrel := (FML.ord_lt_ord_iff (LaurentSeries k) 1 π).mp h
    rw [(Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).vlt_iff_lt] at hrel
    simpa only [map_one] using hrel
  have hπX : (Valued.v π : ℤᵐ⁰) ≤ Valued.v (HahnSeries.single (1 : ℤ) (1 : k)) := by
    rw [LaurentSeries.valuation_single_zpow]
    apply (WithZero.lt_mul_exp_iff_le (y := WithZero.exp (-1)) WithZero.exp_ne_zero).mp
    simpa only [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero] using hπlt
  have hle : FML.ord (LaurentSeries k) (HahnSeries.single (1 : ℤ) (1 : k)) ≤ 1 := by
    calc
      _ ≤ FML.ord (LaurentSeries k) π :=
        (FML.ord_le_ord_iff (LaurentSeries k) _ _).mpr hπX
      _ = 1 := by simpa using hπ
  generalize hn : FML.ord (LaurentSeries k) (HahnSeries.single (1 : ℤ) (1 : k)) = t at *
  cases t with
  | top => simp at hle
  | coe n =>
      norm_cast at hpos hle ⊢
      omega

/-- The power-series variable is an actual uniformizer for FML's existing order. -/
@[simp] theorem ord_X :
    FML.ord (LaurentSeries k) ((PowerSeries.X : PowerSeries k) : LaurentSeries k) = 1 := by
  simpa only [HahnSeries.ofPowerSeries_X] using ord_single_one k

/-- FML's normalized multiplicative valuation has the X-adic value on `X`. -/
@[simp] theorem normalizedValuation_single_one :
    FML.normalizedMultiplicativeValuation (LaurentSeries k)
      (HahnSeries.single (1 : ℤ) (1 : k)) = WithZero.exp (-1) := by
  have hx : (HahnSeries.single (1 : ℤ) (1 : k) : LaurentSeries k) ≠ 0 :=
    HahnSeries.single_ne_zero one_ne_zero
  have hv := (FML.normalizedMultiplicativeValuation (LaurentSeries k)).ne_zero_iff.mpr hx
  have h := ord_single_one k
  rw [FML.ord_of_ne_zero (LaurentSeries k) hx] at h
  have hlog : WithZero.log (FML.normalizedMultiplicativeValuation (LaurentSeries k)
      (HahnSeries.single (1 : ℤ) (1 : k))) = -1 := by
    norm_cast at h
    omega
  rw [← WithZero.exp_log hv, hlog]

/-- Exact multiplicative normalization for every integer Laurent monomial. -/
@[simp] theorem normalizedValuation_single (n : ℤ) :
    FML.normalizedMultiplicativeValuation (LaurentSeries k)
      (HahnSeries.single n (1 : k)) = WithZero.exp (-n) := by
  rw [RatFunc.single_zpow, map_zpow₀, normalizedValuation_single_one,
    ← WithZero.exp_zsmul]
  simp

/-- Laurent monomials have their integer exponent as the existing FML order. -/
@[simp] theorem ord_single (n : ℤ) :
    FML.ord (LaurentSeries k) (HahnSeries.single n (1 : k)) = (n : WithTop ℤ) := by
  rw [FML.ord_of_ne_zero (LaurentSeries k) (HahnSeries.single_ne_zero one_ne_zero),
    normalizedValuation_single]
  simp

/-- The variable in the actual integer ring, using its power-series identification. -/
noncomputable def XInIntegers : FML.ringOfIntegers (LaurentSeries k) :=
  powerSeriesEquivIntegers k PowerSeries.X

omit [Finite k] in
@[simp] theorem XInIntegers_coe :
    ((XInIntegers k : FML.ringOfIntegers (LaurentSeries k)) : LaurentSeries k) =
      ((PowerSeries.X : PowerSeries k) : LaurentSeries k) := rfl

/-- This actual integral element is a uniformizer for FML's order. -/
@[simp] theorem ord_XInIntegers :
    FML.ord (LaurentSeries k) (XInIntegers k : LaurentSeries k) = 1 :=
  ord_X k

@[simp] theorem XInIntegers_mem_maximalIdeal :
    XInIntegers k ∈ IsLocalRing.maximalIdeal (FML.ringOfIntegers (LaurentSeries k)) := by
  rw [FML.mem_maximalIdeal_iff_ord_pos, ord_XInIntegers]
  norm_num

@[simp] theorem residue_XInIntegers :
    IsLocalRing.residue _ (XInIntegers k) = 0 := by
  apply (residueEquiv k).injective
  simp [XInIntegers]

/-- The same monomials expressed as all integer powers of the usual variable. -/
@[simp] theorem ord_X_zpow (n : ℤ) :
    FML.ord (LaurentSeries k)
      (((PowerSeries.X : PowerSeries k) : LaurentSeries k) ^ n) = (n : WithTop ℤ) := by
  rw [HahnSeries.ofPowerSeries_X, ← RatFunc.single_zpow]
  exact ord_single k n

/-- The published residue-normalized absolute value on every integer monomial. -/
@[simp] theorem residueNormalizedAbsoluteValue_single (n : ℤ) :
    LocalField.residueNormalizedAbsoluteValue (LaurentSeries k)
      (HahnSeries.single n (1 : k)) = (Nat.card k : ℝ) ^ (-n) := by
  simpa only [residueCardinality_eq] using
    LocalField.residueNormalizedAbsoluteValue_of_ord_eq (LaurentSeries k) (ord_single k n)

/-- The source normalization is the inverse of the actual residue cardinality. -/
@[simp] theorem residueNormalizedAbsoluteValue_X :
    LocalField.residueNormalizedAbsoluteValue (LaurentSeries k)
      ((PowerSeries.X : PowerSeries k) : LaurentSeries k) = (Nat.card k : ℝ)⁻¹ := by
  simp [HahnSeries.ofPowerSeries_X]

@[simp] theorem residueNormalizedAbsoluteValue_X_zpow (n : ℤ) :
    LocalField.residueNormalizedAbsoluteValue (LaurentSeries k)
      (((PowerSeries.X : PowerSeries k) : LaurentSeries k) ^ n) =
        (Nat.card k : ℝ) ^ (-n) := by
  rw [HahnSeries.ofPowerSeries_X, ← RatFunc.single_zpow]
  exact residueNormalizedAbsoluteValue_single k n

/-- The zero convention is inherited from the published FML order. -/
@[simp] theorem ord_zero : FML.ord (LaurentSeries k) 0 = ⊤ := FML.ord_zero _

namespace ZModTwo

/-- A concrete residue-characteristic-two Laurent-series field. -/
abbrev carrier := LaurentSeries (ZMod 2)

/-- All local-field hypotheses are discharged by the constructed instances. -/
theorem localField : IsNonarchimedeanLocalField carrier := inferInstance

@[simp] theorem residueCardinality : LocalField.residueCardinality carrier = 2 := by
  rw [Laurent.residueCardinality_eq, Nat.card_eq_fintype_card, ZMod.card]

@[simp] theorem ord_X :
    FML.ord carrier ((PowerSeries.X : PowerSeries (ZMod 2)) : carrier) = 1 :=
  Laurent.ord_X (ZMod 2)

@[simp] theorem ord_X_inv :
    FML.ord carrier (((PowerSeries.X : PowerSeries (ZMod 2)) : carrier)⁻¹) =
      ((-1 : ℤ) : WithTop ℤ) := by
  simpa only [zpow_neg_one] using Laurent.ord_X_zpow (ZMod 2) (-1)

@[simp] theorem absoluteValue_X :
    LocalField.residueNormalizedAbsoluteValue carrier
      ((PowerSeries.X : PowerSeries (ZMod 2)) : carrier) = (1 / 2 : ℝ) := by
  simp [Nat.card_eq_fintype_card, ZMod.card]

@[simp] theorem absoluteValue_X_inv :
    LocalField.residueNormalizedAbsoluteValue carrier
      (((PowerSeries.X : PowerSeries (ZMod 2)) : carrier)⁻¹) = 2 := by
  simpa only [zpow_neg_one, neg_neg, zpow_one, Nat.card_eq_fintype_card, ZMod.card,
    Nat.cast_ofNat] using Laurent.residueNormalizedAbsoluteValue_X_zpow (ZMod 2) (-1)

end ZModTwo

end Langlands.LocalField.Laurent
