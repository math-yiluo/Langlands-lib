import Langlands.Representation.Archimedean.RealCharacterInducedSwap
import Langlands.Representation.Archimedean.RealCharacterInducedWeightZero
import Langlands.Representation.Archimedean.RealInducedPairFiltrationReduction

/-!
# The filtration for a character followed by an induction block on `GL₃(ℝ)`

This module assembles `RealCharacterInducedFiltrationStatement` from its cases. Let
`c = sgn^ε |·|^s` and let `d` have weight `m` and exponent `t`, `ℓ = |m|`, with
`Re s < Re t`. Put `w = b - s` with `b = t - ℓ/2`.

* `ℓ = 0`: `RealCharacterInducedWeightZero` with the filtration for two characters;
* `ℓ > 0` and `w` not a nonzero integer: `RealCharacterInducedPushforward.filtration_generic`;
* `ℓ > 0` and `w = k` a positive integer: `RealCharacterInducedPushforward.filtration_reducible`;
* `ℓ > 0` and `w = -m₀` a negative integer: then `m₀ < ℓ / 2` because `Re s < Re t`, and
  `RealCharacterInducedSwap.filtration_tail_first` or `filtration_tail_second` applies,
  according to the parity of `m₀ + ε`.

The result assumes the landing statement `RealSwapLandingStatement` and the uncertainty
statement `RealOrthogonalBlockUncertaintyStatement`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealCharacterInducedFiltration

/-- If `b - s = -m₀` for a natural number `m₀` and `Re s < Re t`, then `m₀ < ℓ`. -/
theorem lt_of_neg (c : RealCharacterData) (d : ComplexCharacterData) (hl : 0 < d.weight.natAbs)
    (hcd : c.exponent.re < d.exponent.re) {m : ℕ}
    (hm : d.exponent - (d.weight.natAbs : ℂ) / 2 - c.exponent = -(m : ℂ)) :
    m < d.weight.natAbs := by
  have hre := congrArg Complex.re hm
  simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re, Complex.div_ofNat_re] at hre
  have hl' : (0 : ℝ) < d.weight.natAbs := by exact_mod_cast hl
  have : (m : ℝ) < d.weight.natAbs := by linarith
  exact_mod_cast this

/-- **The filtration for a character followed by an induction block, conditionally.** Assume
the landing statement and the uncertainty statement. Then
`RealCharacterInducedFiltrationStatement` holds. -/
theorem realCharacterInducedFiltration_of (hL : RealSwapLandingStatement)
    (hU : RealOrthogonalBlockUncertaintyStatement) :
    RealCharacterInducedFiltrationStatement := by
  intro c d hcd
  have hcd' : c.exponent.re < d.exponent.re := hcd
  by_cases hl : d.weight.natAbs = 0
  · exact RealStandardFiltration.realAdjacentFiltration_character_induced_of_weight_eq_zero
      realCharacterPairFiltration c d (Int.natAbs_eq_zero.mp hl) hcd
  have hl0 : 0 < d.weight.natAbs := Nat.pos_of_ne_zero hl
  have hε := c.parity.isLt
  by_cases hint : ∃ k : ℤ, d.exponent - (d.weight.natAbs : ℂ) / 2 - c.exponent = k ∧ k ≠ 0
  · obtain ⟨k, hk, hk0⟩ := hint
    rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · -- case (c): `w = -m₀`
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨k.natAbs, by omega⟩
      have hm : d.exponent - (d.weight.natAbs : ℂ) / 2 - c.exponent = -(m : ℂ) := by
        rw [hk, Int.cast_neg, Int.cast_natCast]
      have hml := lt_of_neg c d hl0 hcd' hm
      have hm0 : 0 < m := by omega
      rcases Nat.mod_two_eq_zero_or_one (m + c.parity.val) with hpar | hpar
      · exact RealCharacterInducedSwap.filtration_tail_second c d hL.2 hU hm0 hml hm hpar
      · exact RealCharacterInducedSwap.filtration_tail_first c d hL.1 hU hm0 hml hm hpar
    · -- case (b): `w = k > 0`
      obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k = (k' : ℤ) := ⟨k.toNat, by omega⟩
      have hk' : (RealCharacterInducedPushforward.chiB d
          (RealCharacterInducedPushforward.fin2 (c.parity.val + k))).exponent -
            c.exponent = (k : ℂ) := by
        rw [RealCharacterInducedPushforward.chiB_exponent, hk, Int.cast_natCast]
      refine RealCharacterInducedPushforward.filtration_reducible c d _ hL.2 hl0
        (k := k) (by omega) hk' ?_
      rw [RealCharacterInducedPushforward.fin2_val]
      omega
  · -- case (a): `w` is not a nonzero integer
    refine RealCharacterInducedPushforward.filtration_generic c d
      (RealCharacterInducedPushforward.fin2 (c.parity.val + 1)) hL.2 hl0 (fun k hk => ?_) ?_
    · by_contra hk0
      exact hint ⟨k, hk, hk0⟩
    · rw [RealCharacterInducedPushforward.fin2_val]
      omega

end RealCharacterInducedFiltration

end Langlands.Archimedean
