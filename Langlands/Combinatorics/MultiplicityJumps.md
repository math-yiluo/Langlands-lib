# Jumps of an antitone integer sequence with prescribed multiplicities

Authors: Worker 146.

This internal helper module supports the proof of
`Langlands.GroupScheme.AlignedSpinCoverTitsIndexStatement` (Task 6282). It is
elementary counting on finite families of integers and cites no outside source. It
supplies the last, purely numerical, step of the index comparison: for a type-`D` chain
of values whose absolute values occur with multiplicities `deg` times those of a family
of `r` values that are pairwise distinct up to sign and nonzero, the positions where the
chain jumps are exactly the multiples `j * deg` with `0 < j ≤ r`.

All declarations are in the namespace `Langlands.Combinatorics.MultiplicityJumps`.
Finite sets are filters of `Finset.univ`, written `#{i | P i}` as in Mathlib.

## Signed counts

- `natCard_signed_eq`: for a finite type `ι`, `f : ι → ℤ` and `v > 0`, the number of
  pairs `(i, s) ∈ ι × ℤˣ` with `s * f i = v` equals `#{i | |f i| = v}`. The map
  `(i, s) ↦ i` is a bijection onto `{i | |f i| = v}`. It is injective because `f i ≠ 0`
  determines `s`, and surjective because `f i = v` or `f i = -v` gives `s = 1` or
  `s = -1`.

## Level sets

Throughout, `a : Fin n → ℤ` and `b : Fin r → ℤ`.

- `mem_iff_lt_card`: a downward closed `s : Finset (Fin n)` is the initial segment
  `{i | i < #s}`. The interval `Iic i` lies in `s` when `i ∈ s`, and `s` lies in `Iio i`
  when `i ∉ s`. Compare cardinalities.
- `card_le_eq`: if `#{i | a i = v} = deg * #{k | b k = v}` for every `v > 0`, then
  `#{i | v ≤ a i} = deg * #{k | v ≤ b k}` for every `v > 0`. Both sides are sums of fibre
  cardinalities over the finite set of values `w ≥ v` taken by `a` or `b`
  (`Finset.card_eq_sum_card_fiberwise`), and the sums agree term by term.
- `card_le_le_succ`: for injective `b`, `#{k | v ≤ b k} ≤ #{k | v + 1 ≤ b k} + 1`,
  since at most one `k` has `b k = v`.
- `exists_card_le_eq`: for positive injective `b` and `0 < j ≤ r` there is `v > 0` with
  `#{k | v ≤ b k} = j`. Let `t` be the least natural number with
  `#{k | 1 + t ≤ b k} < j`. It exists because the level set is empty above `∑ k, b k`.
  It is positive because all `r ≥ j` values are at least `1`. Then `v = 1 + (t - 1)`
  works by minimality of `t` and `card_le_le_succ`.

## The jump lemma

`ne_succ_iff`. Let `a` be nonnegative and antitone, and `b` positive and injective, with
`#{i | a i = v} = deg * #{k | b k = v}` for every `v > 0`. Then for `i + 1 < n`,
`a i ≠ a (i + 1)` if and only if `i + 1 = j * deg` for some `0 < j ≤ r`.

Proof. For each `v`, the set `{l | v ≤ a l}` is downward closed, since `a` is antitone,
so by `mem_iff_lt_card` it is the initial segment of length `#{l | v ≤ a l}`.

- If `a (i + 1) < a i`, take `v = a i > 0`. Position `i` lies in the level set and
  position `i + 1` does not, so the level set has exactly `i + 1` elements. By
  `card_le_eq` this number is `deg * j` with `j = #{k | v ≤ b k}`, so `0 < j ≤ r`.
- Conversely, given `0 < j ≤ r` with `i + 1 = j * deg`, `exists_card_le_eq` gives
  `v > 0` with `#{k | v ≤ b k} = j`. Then `#{l | v ≤ a l} = i + 1` by `card_le_eq`, so
  `v ≤ a i` and `a (i + 1) < v`, and `a i ≠ a (i + 1)`.

## The type-`D` chain

`chain_ne_succ_iff`. Let `2 ≤ n` and `c : Fin n → ℤ` with `c (j + 1) ≤ c j` for
`j + 1 < n` and `0 ≤ c (n - 2) + c (n - 1)`. Let `b : Fin r → ℤ` have `b k ≠ 0` and
`b k ≠ b l`, `b k ≠ -b l` for `k ≠ l`. Suppose that for every `v > 0`
`Nat.card {(i, s) : Fin n × ℤˣ // s * c i = v}` is `deg` times
`Nat.card {(k, s) : Fin r × ℤˣ // s * b k = v}`. Then for `i + 2 < n`,
`c i ≠ c (i + 1)` if and only if `i + 1 = j * deg` for some `0 < j ≤ r`.

Proof. The chain inequalities give `c 0 ≥ … ≥ c (n - 2) ≥ |c (n - 1)|`: the last step
uses `c (n - 1) ≤ c (n - 2)` and `-c (n - 1) ≤ c (n - 2)`. Hence `c j ≥ 0` for
`j + 1 < n`, and `j ↦ |c j|` is antitone. The function `k ↦ |b k|` is positive and
injective by the hypotheses on `b`. By `natCard_signed_eq` the signed-count hypothesis
becomes `#{j | |c j| = v} = deg * #{k | |b k| = v}`. Apply `ne_succ_iff` to `|c|` and
`|b|`. For `i + 2 < n` both `c i` and `c (i + 1)` are nonnegative, so `|c i| = c i` and
`|c (i + 1)| = c (i + 1)`.
