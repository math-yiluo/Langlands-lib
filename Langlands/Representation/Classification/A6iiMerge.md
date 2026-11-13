# Stable merging of exponent-sorted families into equal-exponent groups

Author: Worker 4988. Module `Langlands.Representation.Classification.A6iiMerge`,
namespace `Langlands.Classification.A6ii`. Internal combinatorics for the proof of Tadić's
Corollary A.6(ii) (`IrreducibleLanglandsHeadProductProof`); no literature counterpart.

Let `N` items carry positive degrees `deg : Fin N → ℕ` summing to `n` and real exponents
`ex : Fin N → ℝ`.

- `MergeGrouping n deg ex` (structure) has the following fields:
  - `shape : BlockShape n`, the groups;
  - `exponent`, a strictly decreasing exponent of each group;
  - `count g`, the number of members of each group;
  - `label : (Σ g, Fin (count g)) ≃ Fin N`, the members;
  - `label_exponent`: every member of group `g` has exponent `exponent g`;
  - `size_sum`: the degrees of the members of `g` sum to `shape.size g`;
  - `lt_of_lt`: stability. If the label of `x` is smaller than the label of `y` and
    `ex(label y) ≤ ex(label x)`, then `x` comes before `y` in the group-then-position
    order (`finSigmaFinEquiv`).
- `MergeGrouping.refinement`: the block refinement of `shape` by the member degrees.
- `MergeGrouping.group_monotone` and `MergeGrouping.antitone_exponent`: listed group by
  group, later members lie in the same or later groups, so their exponents decrease.
- `sort_symm_lt`: Mathlib's `Tuple.sort` of `-ex` is a stable decreasing sort.
- `exists_mergeGrouping`: every such family has a merge grouping. Proof: sort by
  `Tuple.sort (fun ℓ => -ex ℓ)` (stable by `Tuple.eq_sort_iff`), then cut the sorted
  family into maximal runs of equal exponent with the published
  `orderedExponentGrouping`. Stability follows from `sort_symm_lt` and the monotonicity
  of the grouping.
