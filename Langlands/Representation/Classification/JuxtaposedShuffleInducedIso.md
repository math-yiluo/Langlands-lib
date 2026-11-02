# Products of shuffled twists of one cuspidal representation

Author: Worker 1032.

This internal helper of the proof of
`Langlands.Classification.JuxtaposedSegmentSocleReverseProductStructure`
(Zelevinsky 1980, Proposition 4.6, step (1), juxtaposed case) makes no literature
assertion. It combines the shuffle combinatorics of
`Classification.JuxtaposedShuffleCombinatorics` with the swap lifting of
`Classification.JuxtaposedSwapLifting`. It assumes no irreducibility or
commutation result: the two-block swap is an explicit hypothesis `hswap`.

Fix `r > 0`, a representation `A` of `GL_r`, and `q, l : ℕ`. For a shuffle set
`S ⊆ Fin (q + l)`, `shuffleExponent S l 0` is the shuffle of the runs
`l, l+1, …, l+q-1` (positions in `S`) and `0, 1, …, l-1` (other positions).

## Results

- `exists_natCast_shuffleExponent`: with first run starting at a natural `a` and
  second run starting at `0`, every shuffle exponent is a natural number.
- `shuffleExponent_add_one_lt_of_move`: if `#S = q`, `i ∈ S`, `j ∉ S`, and the
  exponents at `i` and `j` do not differ by exactly one, then
  `e_S(j) + 1 < e_S(i)`. The strict inequality `e_S(j) < e_S(i)` is
  `shuffleExponent_lt_of_move`, and both sides are naturals.
- `shuffleFamily A S a₀ a₁` is the family `k ↦ ν^(e_S(k)) A` over `Fin m`, valued
  in representations of `GL_r`. It is `shuffleFactors` of
  `TwoSegmentSocleShuffleJacquetStatement` with the indexing of the uniform shape
  unfolded; the two are definitionally equal.
- `shuffleFamily_swapShuffle`: exchanging adjacent positions `i, i+1`, exactly one
  of which lies in `S`, permutes the family by the same transposition
  (`shuffleExponent_swapShuffle`).
- `shuffleFamily_induced_iso` and `shuffle_induced_iso`: assume
  `hswap : ν^a A × ν^b A ≅ ν^b A × ν^a A` along `uniform 2 r` for all natural
  numbers `a, b` with `b + 1 < a`. Then for every `S` with `#S = q` other than the identity shuffle
  `{l, …, l+q-1}`, the product of `ν^(e_S(k)) A` along `uniform (q + l) r` is
  isomorphic to the product for the initial shuffle `{0, …, q-1}`.
  `shuffle_induced_iso` states this for `shuffleFactors`, by definitional
  unfolding.

## Proof of `shuffleFamily_induced_iso`

Induction with `shuffle_induction`, whose motive is "the product for `S` is
isomorphic to the product for the initial shuffle". The base case is the
identity isomorphism. In the step, `S` has a right move `i ∈ S`, `i + 1 ∉ S`
whose exponents do not differ by exactly one, and the inductive hypothesis
gives the isomorphism for `S`. The exponents are natural numbers
(`exists_natCast_shuffleExponent`), and by `shuffleExponent_add_one_lt_of_move`
`hswap` applies to the pair `a = e_S(i)`, `b = e_S(i+1)`. `uniform_adjacentSwap` lifts it
to an isomorphism between the products of the family of `S` and of that family
composed with `(i i+1)`. The second is the family of `swapShuffle S i (i+1)`
(`shuffleFamily_swapShuffle`), and composing with the inductive isomorphism
gives the claim.
