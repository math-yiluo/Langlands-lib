import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! # The tame pairing of an integer-valued valuation -/

open scoped WithZero

namespace Langlands.KTheory

variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)

/-- The additive order of a field unit. An element of valuation `WithZero.exp (-1)`
has order one. -/
def valuationOrder (a : Fˣ) : ℤ := -WithZero.log (v (a : F))

theorem valuation_eq_exp_neg_order (a : Fˣ) :
    v (a : F) = WithZero.exp (-valuationOrder v a) := by
  rw [valuationOrder, neg_neg, WithZero.exp_log ((map_ne_zero v).mpr a.ne_zero)]

theorem valuationOrder_eq_zero_iff (a : Fˣ) :
    valuationOrder v a = 0 ↔ v (a : F) = 1 := by
  rw [valuation_eq_exp_neg_order, WithZero.exp_eq_one, neg_eq_zero]

theorem valuationOrder_mul (a b : Fˣ) :
    valuationOrder v (a * b) = valuationOrder v a + valuationOrder v b := by
  simp [valuationOrder, map_mul, WithZero.log_mul
    ((map_ne_zero v).mpr a.ne_zero) ((map_ne_zero v).mpr b.ne_zero), add_comm]

theorem valuationOrder_zpow (a : Fˣ) (n : ℤ) :
    valuationOrder v (a ^ n) = n * valuationOrder v a := by
  simp [valuationOrder, map_zpow₀, mul_neg]

@[simp]
theorem valuationOrder_neg_one : valuationOrder v (-1 : Fˣ) = 0 := by
  simp [valuationOrder]

@[simp]
theorem valuationOrder_unitGroup (u : v.valuationSubring.unitGroup) :
    valuationOrder v (u : Fˣ) = 0 :=
  (valuationOrder_eq_zero_iff v _).mpr ((Valuation.mem_unitGroup_iff F v _).mp u.property)

/-- The valuation-ring unit represented by Milnor's signed quotient. -/
noncomputable def tameSymbolUnit (a b : Fˣ) : v.valuationSubring.unitGroup := by
  let r := valuationOrder v a
  let s := valuationOrder v b
  refine ⟨(-1 : Fˣ) ^ (r * s) * a ^ s * b ^ (-r),
    (Valuation.mem_unitGroup_iff F v _).mpr ((valuationOrder_eq_zero_iff v _).mp ?_)⟩
  simp only [valuationOrder_mul, valuationOrder_zpow, valuationOrder_neg_one, mul_zero, zero_add,
    neg_mul]
  change s * r + -(r * s) = 0
  rw [mul_comm s r, add_neg_cancel]

@[simp]
theorem coe_tameSymbolUnit (a b : Fˣ) :
    (tameSymbolUnit v a b : Fˣ) =
      (-1 : Fˣ) ^ (valuationOrder v a * valuationOrder v b) *
        a ^ valuationOrder v b * b ^ (-valuationOrder v a) := rfl

theorem val_tameSymbolUnit (a b : Fˣ) :
    ((tameSymbolUnit v a b : Fˣ) : F) =
      (-1 : F) ^ (valuationOrder v a * valuationOrder v b) *
        (a : F) ^ valuationOrder v b * (b : F) ^ (-valuationOrder v a) := by
  simp only [coe_tameSymbolUnit, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.coe_neg_one]

/-- The tame pairing obtained by reducing the signed quotient to the residue field. -/
noncomputable def tameSymbol (a b : Fˣ) : (IsLocalRing.ResidueField v.valuationSubring)ˣ :=
  v.valuationSubring.unitGroupToResidueFieldUnits (tameSymbolUnit v a b)

/-- With a valuation-ring unit in the first argument, the pairing is a power of its reduction. -/
theorem tameSymbol_unitGroup_left (u : v.valuationSubring.unitGroup) (b : Fˣ) :
    tameSymbol v (u : Fˣ) b =
      (v.valuationSubring.unitGroupToResidueFieldUnits u) ^ valuationOrder v b := by
  have h : tameSymbolUnit v (u : Fˣ) b = u ^ valuationOrder v b := by
    apply Subtype.ext
    simp
  rw [tameSymbol, h, map_zpow]

@[simp]
theorem tameSymbol_unitGroup_unitGroup (u w : v.valuationSubring.unitGroup) :
    tameSymbol v (u : Fˣ) (w : Fˣ) = 1 := by
  rw [tameSymbol_unitGroup_left, valuationOrder_unitGroup, zpow_zero]

theorem tameSymbol_unitGroup_uniformizer (u : v.valuationSubring.unitGroup) (π : Fˣ)
    (hπ : valuationOrder v π = 1) :
    tameSymbol v (u : Fˣ) π = v.valuationSubring.unitGroupToResidueFieldUnits u := by
  rw [tameSymbol_unitGroup_left, hπ, zpow_one]

end Langlands.KTheory
