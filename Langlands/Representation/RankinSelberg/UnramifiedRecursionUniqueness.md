# Uniqueness for the minuscule Hecke recursion on partitions

Author: Worker 1797. Module
`Langlands.Representation.RankinSelberg.UnramifiedRecursionUniqueness`, namespace
`Langlands.RankinSelberg.UnramifiedWhittaker`.

This internal helper module serves the proof of
`Langlands.RankinSelberg.UnramifiedSphericalVectorStatement`
(see `UnramifiedSphericalVectorProof.md`). It is pure combinatorics and states no
new proposition about the source.

## Sums of distinct natural numbers

- `sum_range_card_le_and_eq`: for a finite set `T` of natural numbers,
  `0 + 1 + ⋯ + (|T| - 1) ≤ ∑_(i ∈ T) i`, and equality holds only for
  `T = {0, …, |T| - 1}`. Proof by `Finset.induction_on_max`: adding a new maximum
  `a` to `s` adds `a` to the sum, while `a ≥ |s|` because `s ⊆ {0, …, a - 1}`; in the
  equality case `a = |s|` and `s` is an initial segment by induction.
- `sum_range_card_le`, `sum_range_card_lt`: the two parts separately.

## Initial segments of `Fin m`

- `initialSegment m k` is the set of indices `j` with `j < k`.
  `mem_initialSegment`, `map_initialSegment` (its image in `ℕ` is `range k` when
  `k ≤ m`) and `card_initialSegment` (it has `k` elements) are immediate.
- `sum_initialSegment_lt`: a set `S` of size `k` other than the initial segment
  has strictly larger index sum, by transport of `sum_range_card_lt` along
  `Fin.valEmbedding`.
- `eq_initialSegment_of_downward`: a downward closed set `D` equals
  `initialSegment m |D|`. If `j ∈ D` then `D ⊇ [0, j]`, so `|D| > j`; if `j ∉ D`
  then `D ⊆ [0, j)`, so `|D| ≤ j`.

## Partition exponents and the weighted size

- `IsPartitionExponent lam`: `lam : Fin m → ℤ` is antitone and nonnegative.
- `weightedSize lam = ∑ i, (m - i) * lam i` (an integer). It is additive
  (`weightedSize_add`), equals `|S| m - ∑_(i ∈ S) i` on the indicator vector of `S`
  (`weightedSize_subsetExponent`), is nonnegative on nonnegative vectors
  (`weightedSize_nonneg`) and positive on nonzero nonnegative vectors
  (`weightedSize_pos`).

## The recursion

`SatisfiesHeckeRecursion w d`, for weights `w : Finset (Fin m) → ℂ` and
`d : (Fin m → ℤ) → ℂ`, means: for every partition exponent `lam` and every
`1 ≤ k ≤ m` there is a scalar `c` (which may depend on `lam` and `k`) with

`c * d lam = ∑_(|S| = k) w S * d (lam + 1_S)`,

where `1_S` is the published `MinusculeCosets.subsetExponent S`.

`eq_zero_of_satisfiesHeckeRecursion`: suppose the weights of initial segments are
nonzero, `d` satisfies the recursion, `d` vanishes on non-antitone vectors, and
`d 0 = 0`. Then `d` vanishes on every partition exponent.

Proof (strong induction on `N = weightedSize mu`). Let `mu ≠ 0` be a partition
exponent and `D` the set of indices with `mu i > 0`, of size `k ≥ 1`. Since `mu` is
antitone, `D` is downward closed, hence `D = initialSegment m k`. Put
`lam = mu - 1_D`; it is again a partition exponent and `lam + 1_D = mu`. Apply the
recursion at `lam` and `k`:

- `d lam = 0` by induction, since `weightedSize mu = weightedSize lam + weightedSize 1_D`
  with `weightedSize 1_D > 0`;
- for `|S| = k`, `S ≠ D`, the vector `lam + 1_S` is nonnegative and, by
  `sum_initialSegment_lt`, has smaller weighted size than `mu`; so `d` vanishes
  there, by induction if it is antitone and by hypothesis otherwise.

The recursion therefore reduces to `w D * d mu = 0`, and `w D ≠ 0` gives
`d mu = 0`.

## Provenance

Internal (derived). The triangularity of the minuscule Hecke operators on dominant
weights is the mechanism of Shintani's proof (1976) that spherical Whittaker
functions are determined by their value at the identity; the weighted-size
induction is an implementation choice.
