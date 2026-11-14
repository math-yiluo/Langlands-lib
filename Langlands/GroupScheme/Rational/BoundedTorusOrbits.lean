import Langlands.GroupScheme.Rational.BoundedCharacterComponents
import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-! # Laurent functions bounded on uniformizer-power tuples -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.BoundedTorusOrbits

open splitTorus BoundedCharacterComponents

variable {k : Type u} [Field k]
variable (I : Type u) [Fintype I] [DecidableEq I]

/-- Integer tuples give tuples of powers of one unit. -/
def powerTuple (π : kˣ) : Multiplicative (I → ℤ) →* (I → kˣ) where
  toFun n i := π ^ n.toAdd i
  map_one' := by ext i; simp
  map_mul' n m := by ext i; simp [zpow_add]

omit [Fintype I] in
@[simp] theorem powerTuple_single (π : kˣ) (i : I) (n : ℤ) :
    powerTuple I π (Multiplicative.ofAdd (Pi.single i n)) = Pi.mulSingle i (π ^ n) := by
  funext j
  by_cases h : j = i
  · subst j; simp [powerTuple]
  · simp [powerTuple, Pi.single_eq_of_ne h, Pi.mulSingle_eq_of_ne h]

/-- A Laurent character restricted to integer-power tuples. -/
def powerMonomial (π : kˣ) (m : I → ℤ) : Multiplicative (I → ℤ) →* k :=
  (rationalMonomial I m).comp (powerTuple I π)

@[simp] theorem powerMonomial_single (π : kˣ) (m : I → ℤ) (i : I) (n : ℤ) :
    powerMonomial I π m (Multiplicative.ofAdd (Pi.single i n)) =
      ((π ^ n) ^ m i : kˣ) := by
  simp only [powerMonomial, MonoidHom.comp_apply, rationalMonomial,
    MonoidHom.coe_mk, OneHom.coe_mk, powerTuple_single, exponentValue_mulSingle]

omit [DecidableEq I] in
theorem evaluate_powerTuple (π : kˣ) (p : AddMonoidAlgebra k (I → ℤ))
    (n : Multiplicative (I → ℤ)) :
    (Finsupp.linearCombination k
      (fun m => (powerMonomial I π m : Multiplicative (I → ℤ) → k)) p.coeff) n =
      evaluateUnits (R := CommRingCat.of k) I (powerTuple I π n) p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single m c =>
    rw [evaluateUnits_single (R := CommRingCat.of k)]
    simp [powerMonomial, rationalMonomial]

variable (v : Valuation k (WithZero (Multiplicative ℤ))) (π : kˣ)
  (hπ : WithZero.log (v (π : k)) ≠ 0)

include hπ

/-- Nonzero valuation separates the restricted Laurent characters. -/
theorem powerMonomial_injective : Function.Injective (powerMonomial I π) := by
  intro m n h
  funext i
  have hi := congrArg (fun f : Multiplicative (I → ℤ) →* k =>
    f (Multiplicative.ofAdd (Pi.single i 1))) h
  simp only [powerMonomial_single, zpow_one, Units.val_zpow_eq_zpow_val] at hi
  have hv := congrArg (fun x : k => WithZero.log (v x)) hi
  simp only [map_zpow₀, WithZero.log_zpow, zsmul_eq_mul] at hv
  exact mul_right_cancel₀ hπ hv

/-- A bounded multiple of a nonconstant power-grid character is zero. -/
theorem coefficient_eq_zero_of_bounded (m : I → ℤ) (hm : m ≠ 0) (c : k)
    (hc : ∃ b : k, b ≠ 0 ∧ ∀ n : Multiplicative (I → ℤ),
      v (c * powerMonomial I π m n) ≤ v b) : c = 0 := by
  by_contra hc0
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    apply hm
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨b, hb, h⟩ := hc
  let d : ℤ := m i * WithZero.log (v (π : k))
  have hd : d ≠ 0 := mul_ne_zero hi hπ
  have hbound (n : ℤ) : WithZero.log (v c) + n * d ≤ WithZero.log (v b) := by
    have hn := h (Multiplicative.ofAdd (Pi.single i n))
    simp only [powerMonomial_single, Units.val_zpow_eq_zpow_val] at hn
    rw [← zpow_mul] at hn
    have hv := (WithZero.log_le_log
      (v.ne_zero_iff.mpr (mul_ne_zero hc0 (zpow_ne_zero _ π.ne_zero)))
      (v.ne_zero_iff.mpr hb)).mpr hn
    rw [map_mul, WithZero.log_mul (v.ne_zero_iff.mpr hc0)
      (v.ne_zero_iff.mpr (zpow_ne_zero _ π.ne_zero))] at hv
    simp only [map_zpow₀, WithZero.log_zpow, zsmul_eq_mul] at hv
    dsimp [d]
    simpa only [Int.cast_id, mul_assoc] using hv
  rcases lt_or_gt_of_ne hd with hd | hd
  · obtain ⟨n, hn⟩ := exists_lt_nsmul (neg_pos.mpr hd)
      (WithZero.log (v b) - WithZero.log (v c))
    have hh := hbound (-(n : ℤ))
    simp only [nsmul_eq_mul] at hn
    nlinarith
  · obtain ⟨n, hn⟩ := exists_lt_nsmul hd
      (WithZero.log (v b) - WithZero.log (v c))
    have hh := hbound (n : ℤ)
    simp only [nsmul_eq_mul] at hn
    omega

/-- A Laurent function bounded on all integer-power tuples is constant. -/
theorem eq_constant_of_bounded (p : AddMonoidAlgebra k (I → ℤ))
    (hp : ∃ b : k, b ≠ 0 ∧ ∀ n : Multiplicative (I → ℤ),
      v (evaluateUnits (R := CommRingCat.of k) I (powerTuple I π n) p) ≤ v b) :
    p = AddMonoidAlgebra.single 0 (p.coeff 0) := by
  let : ValuativeRel k := ValuativeRel.ofValuation v
  have he : (fun n : Multiplicative (I → ℤ) =>
      evaluateUnits (R := CommRingCat.of k) I (powerTuple I π n) p) =
      ∑ m ∈ p.coeff.support, p.coeff m •
        (powerMonomial I π m : Multiplicative (I → ℤ) → k) := by
    funext n
    exact (evaluate_powerTuple I π p n).symm
  have hs : (∑ m ∈ p.coeff.support, p.coeff m •
      (powerMonomial I π m : Multiplicative (I → ℤ) → k)) ∈ boundedFunctions := by
    rw [← he]
    exact hp
  have hcomp := bounded_character_component (powerMonomial I π)
    (powerMonomial_injective I v π hπ) p.coeff.support p.coeff hs
  apply AddMonoidAlgebra.coeff_injective
  ext m
  by_cases hm : m = 0
  · subst m; simp
  · have hzero : p.coeff m = 0 := by
      by_cases hmem : m ∈ p.coeff.support
      · apply coefficient_eq_zero_of_bounded I v π hπ m hm
        exact hcomp m hmem
      · exact Finsupp.notMem_support_iff.mp hmem
    simp [AddMonoidAlgebra.coeff_single, hm, hzero]

end Langlands.GroupScheme.BoundedTorusOrbits
