import Langlands.Geometry.FormalGroup.HarrisComponentQuotient
import Langlands.Geometry.FormalGroup.HarrisSplitSpecialWeil
import Langlands.LocalField.ResidueNormalization
import Mathlib.NumberTheory.Padics.LocalField

/-! # The scalar order of the inverse Frobenius rigidifier -/

noncomputable section

universe u s

namespace Langlands.FormalGroup.Harris

open scoped WithZero
open ValuativeRel ModuleLaw Langlands.Shimura

variable (p : ℕ) [Fact p.Prime]

/-- The canonical local-field valuation on `ℚ_[p]` sends `p` to `exp (-1)`. -/
private theorem normalizedPadicValuation_p :
    FML.normalizedMultiplicativeValuation ℚ_[p] (p : ℚ_[p]) = WithZero.exp (-1 : ℤ) := by
  let ν := FML.normalizedMultiplicativeValuation ℚ_[p]
  let v := Padic.mulValuation (p := p)
  have hle (a b : ℚ_[p]) : ν a ≤ ν b ↔ v a ≤ v b := by
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt ℚ_[p] (valuation ℚ_[p] a) ≤
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt ℚ_[p] (valuation ℚ_[p] b) ↔ _
    rw [map_le_map_iff, ← (valuation ℚ_[p]).vle_iff_le, v.vle_iff_le]
  have hlt (a b : ℚ_[p]) : ν a < ν b ↔ v a < v b := by
    simp only [lt_iff_not_ge, hle]
  obtain ⟨x, hx⟩ := FML.normalizedMultiplicativeValuation_surjective ℚ_[p] (WithZero.exp (-1 : ℤ))
  change ν x = _ at hx
  have hx0 : x ≠ 0 := ν.ne_zero_iff.mp (hx ▸ WithZero.exp_ne_zero)
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hvx : v x < 1 := by
    have h : ν x < ν 1 := by simp [hx]
    simpa only [map_one] using (hlt x 1).mp h
  have hxp : v x ≤ v (p : ℚ_[p]) := by
    change Padic.mulValuation x < 1 at hvx
    rw [Padic.mulValuation_toFun, ite_eq_right hx0, WithZero.exp_lt_one_iff] at hvx
    change Padic.mulValuation x ≤ Padic.mulValuation (p : ℚ_[p])
    rw [Padic.mulValuation_toFun, Padic.mulValuation_toFun, ite_eq_right hx0, ite_eq_right hp0,
      Padic.valuation_p, WithZero.exp_le_exp]
    omega
  have hp1 : ν (p : ℚ_[p]) < 1 := by
    have h : v (p : ℚ_[p]) < v 1 := by
      simpa only [map_one] using Padic.valuation_p_lt_one v
    simpa only [map_one] using (hlt _ _).mpr h
  have hlower : (-1 : ℤ) ≤ WithZero.log (ν (p : ℚ_[p])) :=
    WithZero.le_log_of_exp_le (hx ▸ (hle x p).mpr hxp)
  have hpν := ν.ne_zero_iff.mpr hp0
  have hupper : WithZero.log (ν (p : ℚ_[p])) < 0 :=
    (WithZero.log_lt_iff_lt_exp hpν).mpr (by simpa only [WithZero.exp_zero] using hp1)
  change ν (p : ℚ_[p]) = _
  rw [← WithZero.exp_log hpν]
  congr 1
  omega

/-- The scalar component order attached to a rigidifier with multiplier `c`
is the normalized valuation order of `c⁻¹`. -/
def inverseMultiplierOrder : ℚ_[p]ˣ →* Multiplicative ℤ where
  toFun c := valuationUnitOrder (FML.normalizedMultiplicativeValuation ℚ_[p]) c⁻¹
  map_one' := by simp
  map_mul' a b := by rw [mul_inv_rev, map_mul, mul_comm]

theorem valuationUnitOrder_frobeniusMultiplier (m : ℕ) :
    valuationUnitOrder (FML.normalizedMultiplicativeValuation ℚ_[p])
      (PolarizedOrderModule.frobeniusMultiplier p m) = Multiplicative.ofAdd (m : ℤ) := by
  have hpow : PolarizedOrderModule.frobeniusMultiplier p m =
      PolarizedOrderModule.frobeniusMultiplier p 1 ^ m := by
    apply Units.ext
    simp
  have hp : valuationUnitOrder (FML.normalizedMultiplicativeValuation ℚ_[p])
      (PolarizedOrderModule.frobeniusMultiplier p 1) = Multiplicative.ofAdd (1 : ℤ) := by
    change Multiplicative.ofAdd (-WithZero.log
      (FML.normalizedMultiplicativeValuation ℚ_[p] ((p : ℚ_[p]) ^ 1))) = _
    rw [pow_one, normalizedPadicValuation_p, WithZero.log_exp, neg_neg]
  rw [hpow, map_pow, hp]
  apply Multiplicative.toAdd.injective
  simp

/-- Precomposition by inverse `m`-fold Frobenius adds `m` to the scalar order. -/
theorem inverseMultiplierOrder_frobenius (c : ℚ_[p]ˣ) (m : ℕ) :
    (inverseMultiplierOrder p ((PolarizedOrderModule.frobeniusMultiplier p m)⁻¹ * c)).toAdd =
      (inverseMultiplierOrder p c).toAdd + m := by
  change (valuationUnitOrder (FML.normalizedMultiplicativeValuation ℚ_[p])
    (((PolarizedOrderModule.frobeniusMultiplier p m)⁻¹ * c)⁻¹)).toAdd = _
  rw [mul_inv_rev, inv_inv, map_mul, valuationUnitOrder_frobeniusMultiplier]
  rfl

section Split

open MulOpposite

variable {D : Type u} [DivisionRing D] [Algebra ℚ_[p] D]

/-- A multiplier-one rigidifier precomposed by the inverse of a split
similitude has inverse multiplier order equal to its second component. -/
theorem inverseMultiplierOrder_eq_splitValuationCoordinates_snd (νD : Valuation D ℤᵐ⁰)
    (g : (splitInvolution ℚ_[p] D).similitudes) :
    inverseMultiplierOrder p ((splitInvolution ℚ_[p] D).multiplier g)⁻¹ =
      (splitValuationCoordinates ℚ_[p] D νD
        (FML.normalizedMultiplicativeValuation ℚ_[p]) g).2 := by
  change valuationUnitOrder (FML.normalizedMultiplicativeValuation ℚ_[p])
    (((splitInvolution ℚ_[p] D).multiplier g)⁻¹)⁻¹ = _
  rw [inv_inv]
  rfl

/-- The inverse multiplier update on a rigidifier agrees with the scalar
coordinate of the right translation in (A.3). -/
theorem inverseMultiplierOrder_eq_weilComponent_snd (νD : Valuation D ℤᵐ⁰)
    (g : (splitInvolution ℚ_[p] D).similitudes) (uniformizer : (Dᵐᵒᵖ)ˣ) (m : ℕ) :
    inverseMultiplierOrder p ((PolarizedOrderModule.frobeniusMultiplier p m)⁻¹ *
      ((splitInvolution ℚ_[p] D).multiplier g)⁻¹) =
      (splitValuationCoordinates ℚ_[p] D νD (FML.normalizedMultiplicativeValuation ℚ_[p])
        (g * weilComponentElement ℚ_[p] D uniformizer
          (PolarizedOrderModule.frobeniusMultiplier p 1) m)).2 := by
  apply Multiplicative.toAdd.injective
  rw [inverseMultiplierOrder_frobenius, inverseMultiplierOrder_eq_splitValuationCoordinates_snd p νD g,
    map_mul, weilComponentElement, splitValuationCoordinates_element, map_pow,
    valuationUnitOrder_frobeniusMultiplier]
  change _ + (m : ℤ) = _ + _
  simp

end Split

section Framing

open CategoryTheory LocalDivision PolarizedFramedAffinePoint

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable [Algebra ℤ_[p] 𝒪[K]]
variable {W : Type} [CommRing W] [Algebra 𝒪[K] W] [Algebra ℤ_[p] W]
variable [wTower : IsScalarTower ℤ_[p] 𝒪[K] W] {ϖ : 𝒪[K]}
variable (frame : SplitPolarizedFrame p K D W ϖ) (σ : W ≃ₐ[𝒪[K]] W)

local instance harrisWeilMultiplierOrderPadicIntegerRingAlgebra : Algebra ℤ_[p] (IntegerRing K D) :=
  Algebra.compHom (IntegerRing K D) (algebraMap ℤ_[p] 𝒪[K])

variable [ExpChar (ResidueRing W (algebraMap 𝒪[K] W ϖ)) p] (m : ℕ)
variable (hσ :
  (Nilp.twistResidueEquiv (σ.restrictScalars ℤ_[p]) (σ.commutes ϖ)).toRingHom =
    iterateFrobenius (ResidueRing W (algebraMap 𝒪[K] W ϖ)) p m)
variable (hF : (frame.order.frobeniusHom p m
    (Nilp.twistResidueEquiv (σ.restrictScalars ℤ_[p]) (σ.commutes ϖ)).toAlgHom hσ).val.IsIsogeny)
variable {T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)}

local notation "πW" => algebraMap 𝒪[K] W ϖ
local notation "σₚ" => AlgEquiv.restrictScalars ℤ_[p] σ
local notation "hπ" => AlgEquiv.commutes σ ϖ

/-- On the actual affine representative of (A.4), any multiplier certificate
gives one whose scalar component order has increased by the Frobenius exponent. -/
theorem splitSpecialWeilFrobeniusPoint_exists_multiplierOrder
    (X : PolarizedFramedAffinePoint p πW frame T) (c : ℚ_[p]ˣ)
    (hc : RationalSection.HasPadicTorsionSimilitude p
      (frame.map (frameCoefficientMap p πW T)).polarization
      X.reducedTarget.polarization X.rho c) :
    let Y := splitSpecialWeilFrobeniusPoint frame σ m hσ hF X
    ∃ d : ℚ_[p]ˣ, RationalSection.HasPadicTorsionSimilitude p
      (frame.map (frameCoefficientMap p πW (Nilp.twistObj σₚ hπ T))).polarization
      Y.reducedTarget.polarization Y.rho d ∧
      (inverseMultiplierOrder p d).toAdd = (inverseMultiplierOrder p c).toAdd + m := by
  exact ⟨_, splitSpecialWeilFrobeniusPoint_hasMultiplier frame σ m hσ hF X c hc,
    inverseMultiplierOrder_frobenius p c m⟩

end Framing

end Langlands.FormalGroup.Harris
