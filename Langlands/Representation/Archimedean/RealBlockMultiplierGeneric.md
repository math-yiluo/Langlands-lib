# The generic multiplier without a condition on the real part

Module `Langlands.Representation.Archimedean.RealBlockMultiplierGeneric`, namespace
`Langlands.Archimedean.RealBlockMultiplier`. It imports only the Library module
`Langlands.Representation.Archimedean.RealBlockMultiplier` (see its Markdown for
`IsRecurrent`, `IsSymmetric`, `extend`, `genericSeq` and `genericMultiplier`).

## Role and provenance

This is internal, elementary algebra with no sources. The Library module
`RealBlockMultiplier` proves its generic results (`isRecurrent_genericMultiplier`,
`genericMultiplier_ne_zero`, `exists_generic`) under `0 < re ν`. That hypothesis is used only
to see that the denominators `ε + 2i + 1 + ν` of
`genericSeq ν ε m = ∏_{i<m} (ε + 2i + 1 - ν) / (ε + 2i + 1 + ν)` do not vanish. This module
replaces it by exactly that condition, `ν ≠ -(ε + 2m + 1)` for all `m : ℕ`.

The variant is needed for the character/character swap of Task 7069
(`Langlands.Archimedean.RealCharacterSwapStatement`): two unlinked characters whose exponents
have the same real part give `re ν = 0`, outside the Library hypothesis. For characters,
unlinked means exactly that `ν` avoids `±(ε + 2m + 1)`, with `ε` the parity of the pair.
The same `genericMultiplier ν ε` is used; only the hypotheses change.

## Definition

* `IsGenericParameter ν ε` (for `ν : ℂ`, `ε : ℤ`):
  `(∀ m : ℕ, ν ≠ ε + 2m + 1) ∧ ∀ m : ℕ, ν ≠ -(ε + 2m + 1)`.
  So `ν` avoids the numbers `±(ε + 2m + 1)`. For `ε ∈ {0, 1}` these are the integers `k` with
  `|k| > ε` and `k - ε` odd. The first conjunct makes the numerators of `genericSeq` nonzero,
  the second its denominators.

## Results

Throughout, `hne : ∀ m : ℕ, ν ≠ ε + 2m + 1` and `hden : ∀ m : ℕ, ν ≠ -(ε + 2m + 1)`.

* `genericSeq_denom_ne_zero_of_ne hden i`: `ε + 2i + 1 + ν ≠ 0`.
* `ne_neg_of_re_nonneg hν hε m`: if `0 ≤ re ν` and `0 ≤ ε`, then `ν ≠ -(ε + 2m + 1)`. So the
  Library hypothesis `0 < re ν` (and even `0 ≤ re ν`) implies `hden`.
* `genericSeq_succ_of_ne hden m`:
  `genericSeq ν ε (m + 1) · (ν + 1 + ε + 2m) = (ε + 2m + 2 - (ν + 1)) · genericSeq ν ε m`.
* `genericSeq_ne_zero_of_ne hne hden m`: `genericSeq ν ε m ≠ 0`.
* `isRecurrent_genericMultiplier_of_ne hε hden` (with `hε : ε = 0 ∨ ε = 1`):
  `IsRecurrent (ν + 1) ε (genericMultiplier ν ε)`.
* `genericMultiplier_ne_zero_of_ne hne hden k`: `genericMultiplier ν ε k ≠ 0` for every
  `k : ℤ`.
* `exists_generic_of_ne hε hne hden`: there is `μ : ℤ → ℂ` with `IsRecurrent (ν + 1) ε μ`,
  `IsSymmetric ε ((-1)^|ε|) μ` and `μ k ≠ 0` for every `k` with `Even (k - ε)`. This is the
  Library `exists_generic` with `0 < re ν` replaced by `hden`.
* `isGenericParameter_of_re_nonneg hν hε hne`: if `0 ≤ re ν` and `0 ≤ ε`, then `hne` alone
  gives `IsGenericParameter ν ε`.
* `IsGenericParameter.exists_generic hε h`: the conclusion of `exists_generic_of_ne` from
  `h : IsGenericParameter ν ε`.

## Proofs

* `genericSeq_denom_ne_zero_of_ne`: if `ε + 2i + 1 + ν = 0`, then `ν = -(ε + 2i + 1)`
  (`linear_combination`), contradicting `hden i`.
* `ne_neg_of_re_nonneg`: taking real parts of `ν = -(ε + 2m + 1)` gives
  `re ν = -(ε + 2m + 1) < 0` (`linarith` with `0 ≤ ε`, `0 ≤ m`).
* `genericSeq_succ_of_ne`: `Finset.prod_range_succ` splits off the factor
  `(ε + 2m + 1 - ν) / (ε + 2m + 1 + ν)`; its denominator is nonzero, so `field_simp` and
  `ring` close the identity. This is the Library proof with the real-part argument replaced.
* `genericSeq_ne_zero_of_ne`: `Finset.prod_ne_zero_iff`; each factor is a quotient of the
  nonzero numerator `ε + 2i + 1 - ν` (by `hne i`) by a nonzero denominator.
* `isRecurrent_genericMultiplier_of_ne`: the Library `isRecurrent_extend` with
  `σ = (-1)^|ε|` (so `σ² = 1` by `neg_one_pow_sq` and the centre condition holds by the second
  alternative), and the sequence identity from `genericSeq_succ_of_ne`
  (`linear_combination`).
* `genericMultiplier_ne_zero_of_ne`: the Library `extend_ne_zero_iff` with `σ ≠ 0` reduces it
  to `genericSeq_ne_zero_of_ne`.
* `exists_generic_of_ne` takes `μ = genericMultiplier ν ε`, with the Library
  `isSymmetric_genericMultiplier` (which has no hypothesis on `ν`) for the symmetry.
* `isGenericParameter_of_re_nonneg` pairs `hne` with `ne_neg_of_re_nonneg`, and
  `IsGenericParameter.exists_generic` applies `exists_generic_of_ne` to the two conjuncts.
