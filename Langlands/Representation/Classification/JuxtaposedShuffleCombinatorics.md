# Shuffle combinatorics for two juxtaposed segments

Author: Worker 1032.

This internal helper of the proof of
`Langlands.Classification.JuxtaposedSegmentSocleReverseProductStructure` is pure
finite combinatorics about the shuffle exponents `shuffleExponent S a₀ a₁` of
`Classification.TwoSegmentSocleShuffleJacquetStatement`. It makes no
representation-theoretic or literature assertion. Recall that for
`S ⊆ Fin m`, position `k ∈ S` gets `a₀ + #{x ∈ S | x < k}` and position `k ∉ S`
gets `a₁ + #{x ∉ S | x < k}`.

## Adjacent transpositions

- `swapShuffle S i j` is the image of `S` under the transposition `(i j)`;
  `mem_swapShuffle`, `card_swapShuffle`, `swapShuffle_swapShuffle` and
  `compl_swapShuffle` are its basic properties.
- `swap_lt_swap_iff`: an adjacent transposition (`j = i + 1`) preserves the order
  of every pair other than `{i, j}`.
- `shuffleExponent_swapShuffle(_apply)`: if `j = i + 1` and exactly one of `i`,
  `j` lies in `S`, then `e_{swapShuffle S i j}(k) = e_S((i j) k)`. The positions
  counted below `k` are carried bijectively by the transposition, because the
  only pair whose order changes is `{i, j}`, which does not lie in one of `S`, `Sᶜ`
  (`card_filter_swapShuffle`).

## The juxtaposed runs

Now `m = q + p`, `#S = q`, `a₀ = p` and `a₁ = 0`: the positions in `S` carry
`p, …, p+q-1` and the others carry `0, …, p-1`.

- `initShuffle q p = {0, …, q-1}` and `idShuffle q p = {p, …, p+q-1}`, with
  `card_initShuffle`, `card_idShuffle`, `initShuffle_ne_idShuffle` (for
  `q, p > 0`) and `shuffleExponent_initShuffle_zero` (the first exponent of the
  initial shuffle is `p`). The identity shuffle has exponents `0, 1, …, p+q-1`.
- `mem_iff_le_shuffleExponent`: `k ∈ S` iff `p ≤ e_S(k)` (from
  `le_shuffleExponent` and `shuffleExponent_lt`). Hence
  `eq_of_shuffleExponent_eq`: `S` is determined by its exponents.
- `shuffleExponent_lt_of_move`: for `i ∈ S` and `j ∉ S`, `e_S(j) < e_S(i)`.
- `swapShuffle_eq_idShuffle_of_gap`: if `j = i + 1`, `i ∈ S`, `j ∉ S` and
  `e_S(i) = e_S(j) + 1`, then `swapShuffle S i j` is the identity shuffle. Indeed
  `e_S(i) = p + #{x ∈ S | x < i}` and `e_S(j) < p` force no element of `S` below
  `i`, `e_S(j) = p - 1`, so all positions below `i` and `j` itself are the whole
  of `Sᶜ` and everything above `j` lies in `S`.
- `exists_left_move`: if `S` is not an initial segment `{0, …, #S - 1}`, there is
  an adjacent pair `i ∉ S`, `i + 1 ∈ S`.

## Induction over shuffles

`shuffle_induction`: let `P` be a predicate on shuffle sets, true for the initial
shuffle and preserved by every right move `S ↦ swapShuffle S i (i+1)` with
`#S = q`, `i ∈ S`, `i + 1 ∉ S` and `e_S(i) ≠ e_S(i+1) + 1`. Then `P S` holds for
every `S` with `#S = q` other than the identity shuffle.

The proof is strong induction on `∑_{k ∈ S} k`. If `S` is not the initial
shuffle, `exists_left_move` gives `i ∉ S`, `i + 1 ∈ S`. The set
`S' = swapShuffle S i (i+1)` has a smaller sum, is not the identity shuffle (it
contains `i` and not `i + 1`, while the identity shuffle is an upper interval),
and the right move `i ∈ S'`, `i + 1 ∉ S'` brings it back to `S`. That move does
not produce the identity shuffle, because `S` is not it, so by
`swapShuffle_eq_idShuffle_of_gap` its exponents do not differ by exactly one,
and the hypothesis on `P` applies.
