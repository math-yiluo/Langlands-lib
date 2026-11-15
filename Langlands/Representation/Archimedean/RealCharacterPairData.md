# Bookkeeping for a pair of real characters

Module `Langlands.Representation.Archimedean.RealCharacterPairData`, namespace
`Langlands.Archimedean.RealCharacterPair`. It imports `RealLanglandsRankOneReduction`
(`realExponentSupport`, `realBlockSupport`, `realWeightSquareSum`, `realBlockWeightSquare`) and
`ComplexJacquetBorel` (`characterOfParams`).

## Role and provenance

This is internal infrastructure. It makes no claim from the literature and has no sources. It
serves the proof of `Langlands.Archimedean.RealCharacterPairFiltrationStatement` (Task 7067).
There, `x = character c` and `y = character d` are two characters of `ℝ^×` with
`Re t_c < Re t_d`. The proof splits into a generic case, where the standard modules of
`pre ++ [x, y] ++ post` and `pre ++ [y, x] ++ post` are isomorphic, and a reducible case,
where `t_d - t_c` is a positive integer `ℓ` of the right parity. In the reducible case the
filtration uses the real induction of the complex character `pairInduced c d ℓ`. This module
holds the arithmetic of that split: the parity of the pair, the case distinction, and the two
conditions that `RealAdjacentFiltration` imposes on the list `[induced (pairInduced c d ℓ)]`.
Everything is elementary. The module constructs no maps between standard modules.

## Notation

For `c : RealCharacterData` (Library `ArchimedeanAttachment`), `c.character : ℝˣ →ₜ* ℂˣ` is
the character `x ↦ (x/|x|)^{ε_c} |x|^{t_c}`, with `ε_c = c.parity : Fin 2` and
`t_c = c.exponent : ℂ`, as fixed by the field `c.character_eq`. Likewise for `d`.

## Definitions

* `pairInduced c d ℓ : ComplexCharacterData` for `ℓ : ℕ` is
  `characterOfParams (ℓ : ℤ) ((c.exponent + d.exponent) / 2)`. This is the complex character
  `z ↦ (z/‖z‖)^ℓ ‖z‖^{2t}` with `t = (t_c + t_d)/2`, so its weight is `ℓ` and its exponent is
  `(t_c + t_d)/2` (simp lemmas `pairInduced_weight` and `pairInduced_exponent`, both `rfl`).
* `pairParity c d : ℤ` is `((ε_c + ε_d) % 2 : ℕ)` cast to `ℤ`, where `ε_c = c.parity.val`.

## Results

* `pairParity_eq c d : pairParity c d = 0 ∨ pairParity c d = 1`.
* `character_neg_one c : (c.character (-1) : ℂ) = (-1) ^ c.parity.val`.
* `neg_one_pow_pairParity c d :
  (-1 : ℂ) ^ pairParity c d = (c.character (-1) : ℂ) * (d.character (-1) : ℂ)`. The power on the
  left is an integer power (`zpow`). It is the form of the parity hypothesis `hpar` in
  `RealBlockJacquetFunctional`.
* `realExponentSupport_pairInduced_eq (h : d.exponent - c.exponent = ℓ)`: the exponent support
  of `[RealBlock.induced (pairInduced c d ℓ)]` is `[d.exponent, c.exponent]`.
  `realBlockSupport` gives `[t + ℓ/2, t - ℓ/2]` with `t = (t_c + t_d)/2`, and these are `t_d`
  and `t_c` when `t_d - t_c = ℓ`.
* `realExponentSupport_character_pair c d`: the exponent support of
  `[RealBlock.character c, RealBlock.character d]` is `[c.exponent, d.exponent]`.
* `realExponentSupport_pairInduced (h : d.exponent - c.exponent = ℓ)`:
  `(realExponentSupport [RealBlock.induced (pairInduced c d ℓ)]).Perm
  (realExponentSupport [RealBlock.character c, RealBlock.character d])`. The two lists are
  `[t_d, t_c]` and `[t_c, t_d]`, and `List.Perm.swap` relates them.
* `realWeightSquareSum_lt_pairInduced c d (hℓ : 0 < ℓ)`:
  `realWeightSquareSum [RealBlock.character c, RealBlock.character d] <
  realWeightSquareSum [RealBlock.induced (pairInduced c d ℓ)]`. The left side is `0`, since
  characters have squared weight `0`. The right side is `ℓ^2`, since the weight is `ℓ`.
* `exponent_sub_re_pos (h : c.exponent.re < d.exponent.re) : 0 < (d.exponent - c.exponent).re`.
  This is the hypothesis `hν` of `RealBlockMultiplier.exists_generic` for
  `ν = t_d - t_c`.
* `generic_or_reducible c d`: either
  `∀ m : ℕ, d.exponent - c.exponent ≠ (pairParity c d : ℂ) + 2 * m + 1`, or
  `∃ ℓ : ℕ, 0 < ℓ ∧ Even ((ℓ : ℤ) - 1 - pairParity c d) ∧ d.exponent - c.exponent = ℓ`.
  The first alternative is the hypothesis `hne` of `RealBlockMultiplier.exists_generic` with
  `ν = t_d - t_c` and `ε = pairParity c d`. The second gives the hypotheses `hℓ` and `hpar` of
  `RealBlockMultiplier.exists_binomial` and `exists_tail`, together with `t_d - t_c = ℓ`. No
  hypothesis on the real parts is needed for this case distinction.

## Proofs

The support and weight statements unfold `realExponentSupport`, `realBlockSupport`,
`realWeightSquareSum` and `realBlockWeightSquare` with `simp only`, using
`(ℓ : ℤ).natAbs = ℓ` and the two identities `(t_c + t_d)/2 ± ℓ/2 = t_d, t_c`. These follow from
`t_d - t_c = ℓ` by `ring`. `character_neg_one` evaluates `c.character_eq` at `-1`:
`(-1)/|-1| = -1` and `1^{t_c} = 1`. `neg_one_pow_pairParity` then uses
`(-1)^a (-1)^b = (-1)^{a+b}` and `neg_one_pow_eq_pow_mod_two`. For `generic_or_reducible`, if
`t_d - t_c = ε + 2m + 1` with `ε = pairParity c d ∈ {0, 1}`, then
`ℓ = ε.toNat + 2m + 1` works: `ℓ - 1 - ε = 2m`, and the cast identity follows from
`(ε.toNat : ℤ) = ε`. Otherwise the first alternative holds by definition.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
