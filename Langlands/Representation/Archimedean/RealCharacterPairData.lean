import Langlands.Representation.Archimedean.RealLanglandsRankOneReduction
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-!
# Bookkeeping for a pair of real characters

Combinatorial facts about two characters `c = sgn^{ε_c} |·|^{t_c}` and
`d = sgn^{ε_d} |·|^{t_d}` of `ℝ^×`, used in the proof of
`RealCharacterPairFiltrationStatement`.

* `pairInduced c d ℓ` is the complex character `(z/|z|)^ℓ |z|^{t_c + t_d}`, that is
  `characterOfParams ℓ ((t_c + t_d) / 2)`. When `t_d - t_c = ℓ`, its real induction has the
  exponent support `[t_d, t_c]`, a permutation of that of `[c, d]`
  (`realExponentSupport_pairInduced`), and for `0 < ℓ` a strictly larger sum of squared weights
  (`realWeightSquareSum_lt_pairInduced`).
* `pairParity c d ∈ {0, 1}` is `ε_c + ε_d mod 2`, with
  `(-1)^(pairParity c d) = c(-1) d(-1)` (`neg_one_pow_pairParity`).
* `generic_or_reducible`: either `t_d - t_c ≠ pairParity c d + 2m + 1` for every `m : ℕ`, or
  `t_d - t_c = ℓ` for a positive integer `ℓ` with `ℓ - 1 ≡ pairParity c d (mod 2)`. These are
  the hypotheses of `RealBlockMultiplier.exists_generic` and of
  `RealBlockMultiplier.exists_binomial` / `exists_tail` with `ν = t_d - t_c`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealCharacterPair

open Langlands.LocalFactor.Archimedean

/-! ## The induced block of the pair -/

/-- The complex character `z ↦ (z/|z|)^ℓ |z|^{t_c + t_d}` attached to two real characters `c`, `d`
with exponents `t_c`, `t_d` and a natural number `ℓ`: weight `ℓ` and exponent
`(t_c + t_d) / 2`. -/
def pairInduced (c d : RealCharacterData) (ℓ : ℕ) : ComplexCharacterData :=
  characterOfParams (ℓ : ℤ) ((c.exponent + d.exponent) / 2)

@[simp]
theorem pairInduced_weight (c d : RealCharacterData) (ℓ : ℕ) :
    (pairInduced c d ℓ).weight = ℓ :=
  rfl

@[simp]
theorem pairInduced_exponent (c d : RealCharacterData) (ℓ : ℕ) :
    (pairInduced c d ℓ).exponent = (c.exponent + d.exponent) / 2 :=
  rfl

/-- The exponent support of the real induction of `pairInduced c d ℓ` is `[t_d, t_c]` when
`t_d - t_c = ℓ`. -/
theorem realExponentSupport_pairInduced_eq {c d : RealCharacterData} {ℓ : ℕ}
    (h : d.exponent - c.exponent = ℓ) :
    realExponentSupport [RealBlock.induced (pairInduced c d ℓ)] = [d.exponent, c.exponent] := by
  have hn : (((ℓ : ℤ).natAbs : ℕ) : ℂ) = (ℓ : ℂ) := by simp
  have h1 : (c.exponent + d.exponent) / 2 + (ℓ : ℂ) / 2 = d.exponent := by
    rw [← h]; ring
  have h2 : (c.exponent + d.exponent) / 2 - (ℓ : ℂ) / 2 = c.exponent := by
    rw [← h]; ring
  simp only [realExponentSupport, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    realBlockSupport, pairInduced_weight, pairInduced_exponent, hn, h1, h2]

/-- The exponent support of `[c, d]` is `[t_c, t_d]`. -/
theorem realExponentSupport_character_pair (c d : RealCharacterData) :
    realExponentSupport [RealBlock.character c, RealBlock.character d] =
      [c.exponent, d.exponent] := by
  simp only [realExponentSupport, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    realBlockSupport, List.singleton_append]

/-- When `t_d - t_c = ℓ`, the real induction of `pairInduced c d ℓ` has the exponent support of
`[c, d]` up to order. -/
theorem realExponentSupport_pairInduced {c d : RealCharacterData} {ℓ : ℕ}
    (h : d.exponent - c.exponent = ℓ) :
    (realExponentSupport [RealBlock.induced (pairInduced c d ℓ)]).Perm
      (realExponentSupport [RealBlock.character c, RealBlock.character d]) := by
  rw [realExponentSupport_pairInduced_eq h, realExponentSupport_character_pair]
  exact List.Perm.swap _ _ _

/-- For `0 < ℓ`, the sum of squared weights of the real induction of `pairInduced c d ℓ`,
namely `ℓ^2`, exceeds that of `[c, d]`, namely `0`. -/
theorem realWeightSquareSum_lt_pairInduced (c d : RealCharacterData) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    realWeightSquareSum [RealBlock.character c, RealBlock.character d] <
      realWeightSquareSum [RealBlock.induced (pairInduced c d ℓ)] := by
  simp only [realWeightSquareSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    realBlockWeightSquare, pairInduced_weight, Int.natAbs_natCast]
  simpa using pow_pos hℓ 2

/-! ## The parity of the pair -/

/-- The parity of the pair: `ε_c + ε_d mod 2`, as an integer in `{0, 1}`. -/
def pairParity (c d : RealCharacterData) : ℤ :=
  (((c.parity.val + d.parity.val) % 2 : ℕ) : ℤ)

theorem pairParity_eq (c d : RealCharacterData) : pairParity c d = 0 ∨ pairParity c d = 1 := by
  unfold pairParity
  omega

/-- A real character `sgn^ε |·|^t` takes the value `(-1)^ε` at `-1`. -/
theorem character_neg_one (c : RealCharacterData) :
    (c.character (-1) : ℂ) = (-1) ^ c.parity.val := by
  rw [c.character_eq]
  simp

/-- `(-1)^(pairParity c d) = c(-1) d(-1)`. The power is an integer power. -/
theorem neg_one_pow_pairParity (c d : RealCharacterData) :
    (-1 : ℂ) ^ pairParity c d = (c.character (-1) : ℂ) * (d.character (-1) : ℂ) := by
  rw [character_neg_one, character_neg_one, ← pow_add, pairParity, zpow_natCast,
    ← neg_one_pow_eq_pow_mod_two]

/-! ## The generic and the reducible case -/

/-- For `Re t_c < Re t_d`, the difference `t_d - t_c` has positive real part. -/
theorem exponent_sub_re_pos {c d : RealCharacterData} (h : c.exponent.re < d.exponent.re) :
    0 < (d.exponent - c.exponent).re := by
  rw [Complex.sub_re]
  linarith

/-- Either `t_d - t_c` avoids every value `pairParity c d + 2m + 1` (`m : ℕ`), or it is a
positive integer `ℓ` with `ℓ - 1 ≡ pairParity c d (mod 2)`. -/
theorem generic_or_reducible (c d : RealCharacterData) :
    (∀ m : ℕ, d.exponent - c.exponent ≠ (pairParity c d : ℂ) + 2 * m + 1) ∨
      ∃ ℓ : ℕ, 0 < ℓ ∧ Even ((ℓ : ℤ) - 1 - pairParity c d) ∧
        d.exponent - c.exponent = ℓ := by
  by_cases hm : ∃ m : ℕ, d.exponent - c.exponent = (pairParity c d : ℂ) + 2 * m + 1
  · right
    obtain ⟨m, hm⟩ := hm
    have h01 := pairParity_eq c d
    have he : ((pairParity c d).toNat : ℤ) = pairParity c d := Int.toNat_of_nonneg (by omega)
    have hc : (((pairParity c d).toNat : ℕ) : ℂ) = (pairParity c d : ℂ) := by exact_mod_cast he
    refine ⟨(pairParity c d).toNat + 2 * m + 1, by omega, ⟨m, by push_cast; omega⟩, ?_⟩
    rw [hm]
    push_cast
    rw [hc]
  · left
    intro m hm'
    exact hm ⟨m, hm'⟩

end Langlands.Archimedean.RealCharacterPair
