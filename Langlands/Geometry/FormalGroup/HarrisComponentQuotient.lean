import Langlands.LocalFactor.FML.Valuation
import Langlands.Geometry.FormalGroup.HarrisSplitSimilitudes
import Langlands.Algebra.LocalDivisionValuation
import Mathlib.Algebra.Group.Units.Opposite
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The valuation quotient of the split local similitude group -/

noncomputable section
universe u v

namespace Langlands.FormalGroup.Harris
open MulOpposite
open scoped WithZero

section Order

variable {A : Type*} [DivisionRing A]

/-- The additive order of a unit for a multiplicative discrete valuation. -/
def valuationUnitOrder (ν : Valuation A ℤᵐ⁰) : Aˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (-WithZero.log (ν (a : A)))
  map_one' := by simp
  map_mul' a b := by
    change Multiplicative.ofAdd (-WithZero.log (ν ((a : A) * (b : A)))) = _
    rw [map_mul, WithZero.log_mul (ν.ne_zero_iff.mpr a.ne_zero) (ν.ne_zero_iff.mpr b.ne_zero)]
    exact congrArg Multiplicative.ofAdd (neg_add _ _)

theorem valuationUnitOrder_eq_one_iff (ν : Valuation A ℤᵐ⁰) (a : Aˣ) :
    valuationUnitOrder ν a = 1 ↔ ν (a : A) = 1 := by
  constructor
  · intro ha
    have h : -WithZero.log (ν (a : A)) = 0 := congrArg Multiplicative.toAdd ha
    rw [← WithZero.exp_log (ν.ne_zero_iff.mpr a.ne_zero), neg_eq_zero.mp h, WithZero.exp_zero]
  · intro h
    change Multiplicative.ofAdd (-WithZero.log (ν (a : A))) = 1
    rw [h, WithZero.log_one, neg_zero]
    rfl

/-- The order on opposite units uses the same valuation on the original algebra. -/
def oppositeUnitOrder (ν : Valuation A ℤᵐ⁰) : (Aᵐᵒᵖ)ˣ →* Multiplicative ℤ where
  toFun a := valuationUnitOrder ν (Units.opEquiv a).unop
  map_one' := by simp
  map_mul' a b := by
    change valuationUnitOrder ν (Units.opEquiv (a * b)).unop =
      valuationUnitOrder ν (Units.opEquiv a).unop * valuationUnitOrder ν (Units.opEquiv b).unop
    rw [map_mul, unop_mul, map_mul, mul_comm]

theorem oppositeUnitOrder_eq_one_iff (ν : Valuation A ℤᵐ⁰) (a : (Aᵐᵒᵖ)ˣ) :
    oppositeUnitOrder ν a = 1 ↔ ν (unop (a : Aᵐᵒᵖ)) = 1 :=
  valuationUnitOrder_eq_one_iff ν (Units.opEquiv a).unop

end Order

section Split

variable (k : Type u) (B : Type v) [Field k] [DivisionRing B] [Algebra k B]
variable (νB : Valuation B ℤᵐ⁰) (νk : Valuation k ℤᵐ⁰)

/-- The two orders of a split similitude are those of its first unit and multiplier. -/
def splitValuationCoordinates :
    (splitInvolution k B).similitudes →* Multiplicative ℤ × Multiplicative ℤ where
  toFun g :=
    (oppositeUnitOrder νB (splitSimilitudeCoordinates k B g).1,
      valuationUnitOrder νk (splitSimilitudeCoordinates k B g).2)
  map_one' := by simp
  map_mul' g h := by simp

@[simp]
theorem splitValuationCoordinates_element (a : (Bᵐᵒᵖ)ˣ) (e : kˣ) :
    splitValuationCoordinates k B νB νk (splitSimilitudeElement k B a e) =
      (oppositeUnitOrder νB a, valuationUnitOrder νk e) := by
  change (oppositeUnitOrder νB ((splitSimilitudeCoordinates k B)
      ((splitSimilitudeCoordinates k B).symm (a, e))).1,
    valuationUnitOrder νk ((splitSimilitudeCoordinates k B)
      ((splitSimilitudeCoordinates k B).symm (a, e))).2) = _
  rw [MulEquiv.apply_symm_apply]

theorem mem_splitValuationKernel (g : (splitInvolution k B).similitudes) :
    g ∈ (splitValuationCoordinates k B νB νk).ker ↔
      νB (unop ((g.val.1 : Bᵐᵒᵖ × B)).1) = 1 ∧
        νk ((splitInvolution k B).multiplier g : k) = 1 := by
  change (oppositeUnitOrder νB (splitSimilitudeCoordinates k B g).1,
    valuationUnitOrder νk (splitSimilitudeCoordinates k B g).2) = (1, 1) ↔ _
  rw [Prod.mk.injEq, oppositeUnitOrder_eq_one_iff, valuationUnitOrder_eq_one_iff,
    splitSimilitudeCoordinates_fst, splitSimilitudeCoordinates_snd]

/-- The quotient by the common kernel of the two valuation orders. -/
abbrev ValuationComponentGroup :=
  (splitInvolution k B).similitudes ⧸ (splitValuationCoordinates k B νB νk).ker

variable (uniformizer : (Bᵐᵒᵖ)ˣ) (p : kˣ)
variable (hB : oppositeUnitOrder νB uniformizer = Multiplicative.ofAdd (1 : ℤ))
variable (hk : valuationUnitOrder νk p = Multiplicative.ofAdd (1 : ℤ))

/-- Units of order one in both factors give all integer coordinates of the quotient. -/
def valuationComponentEquiv :
    ValuationComponentGroup k B νB νk ≃* Multiplicative ℤ × Multiplicative ℤ :=
  QuotientGroup.quotientKerEquivOfRightInverse _
    (fun z => splitSimilitudeElement k B (uniformizer ^ z.1.toAdd) (p ^ z.2.toAdd))
    (by
      intro z
      rw [splitValuationCoordinates_element, map_zpow, map_zpow, hB, hk]
      apply Prod.ext <;> apply Multiplicative.toAdd.injective <;> simp)

@[simp]
theorem valuationComponentEquiv_mk (g : (splitInvolution k B).similitudes) :
    valuationComponentEquiv k B νB νk uniformizer p hB hk (QuotientGroup.mk g) =
      splitValuationCoordinates k B νB νk g := rfl

include hB hk in
theorem splitValuationCoordinates_weil (g : (splitInvolution k B).similitudes) (f : ℕ) :
    splitValuationCoordinates k B νB νk (g * weilComponentElement k B uniformizer p f) =
      splitValuationCoordinates k B νB νk g *
        (Multiplicative.ofAdd (1 : ℤ), Multiplicative.ofAdd (f : ℤ)) := by
  rw [map_mul, weilComponentElement, splitValuationCoordinates_element, hB, map_pow, hk]
  congr 1
  apply Prod.ext
  · rfl
  · apply Multiplicative.toAdd.injective
    simp

include hB in
theorem splitValuationCoordinates_determinant (g : (splitInvolution k B).similitudes)
    (detOrder : ℤ) :
    splitValuationCoordinates k B νB νk (g * determinantComponentElement k B uniformizer detOrder) =
      splitValuationCoordinates k B νB νk g * (Multiplicative.ofAdd (-detOrder), 1) := by
  rw [map_mul, determinantComponentElement, splitValuationCoordinates_element, map_zpow, hB,
    (valuationUnitOrder νk).map_one]
  congr 1
  apply Prod.ext
  · apply Multiplicative.toAdd.injective
    simp
  · rfl

theorem valuationComponentEquiv_mul_weil (x : ValuationComponentGroup k B νB νk) (f : ℕ) :
    valuationComponentEquiv k B νB νk uniformizer p hB hk
      (x * QuotientGroup.mk (weilComponentElement k B uniformizer p f)) =
    valuationComponentEquiv k B νB νk uniformizer p hB hk x *
      (Multiplicative.ofAdd (1 : ℤ), Multiplicative.ofAdd (f : ℤ)) := by
  rw [map_mul, valuationComponentEquiv_mk]
  have h := splitValuationCoordinates_weil k B νB νk uniformizer p hB hk 1 f
  simpa only [one_mul, map_one] using congrArg
    (fun z => valuationComponentEquiv k B νB νk uniformizer p hB hk x * z) h

theorem valuationComponentEquiv_mul_determinant (x : ValuationComponentGroup k B νB νk)
    (detOrder : ℤ) :
    valuationComponentEquiv k B νB νk uniformizer p hB hk
      (x * QuotientGroup.mk (determinantComponentElement k B uniformizer detOrder)) =
    valuationComponentEquiv k B νB νk uniformizer p hB hk x *
      (Multiplicative.ofAdd (-detOrder), 1) := by
  rw [map_mul, valuationComponentEquiv_mk]
  have h := splitValuationCoordinates_determinant k B νB νk uniformizer hB 1 detOrder
  simpa only [one_mul, map_one] using congrArg
    (fun z => valuationComponentEquiv k B νB νk uniformizer p hB hk x * z) h

end Split

section LocalField

open ValuativeRel Langlands.CentralDivision

variable (k F B : Type u)
variable [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [DivisionRing B] [Algebra k B] [Algebra F B] [FiniteDimensional F B] [Algebra.IsCentral F B]

/-- The actual local-field orders use reduced norm over F and the valuation of the scalar field. -/
def localSplitValuationCoordinates :
    (splitInvolution k B).similitudes →* Multiplicative ℤ × Multiplicative ℤ :=
  splitValuationCoordinates k B (localReducedNormIntValuation F B)
    (Langlands.FML.normalizedMultiplicativeValuation k)

end LocalField
end Langlands.FormalGroup.Harris
