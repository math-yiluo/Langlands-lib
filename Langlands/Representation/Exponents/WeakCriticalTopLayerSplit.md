# Splitting one block of a standard shape along a flattened refinement

Module `Langlands.Representation.Exponents.WeakCriticalTopLayerSplit`.
Internal combinatorial helper module (no source statement); author Worker 728.

## Setting

`B : BlockShape n` and `D : BlockRefinement B`. Flattened blocks of
`B.flatten D` are labelled by pairs (outer block `j`, inner block of `D j`)
through `B.flattenBlockEquiv D`. The Library map `B.flattenOuter D`
(`Classification/MaximalConeLifting`) gives the outer block. Fix an outer block
`j` and an inner block `i` of `D j` that is not the last one
(`hi : i.val + 1 < (D j).length`).

## Declarations

- `refinement_length_pos`: every `D j` has at least one block, since its sizes
  sum to `B.size j > 0`.
- `splitCut D j i := B.flattenBlockEquiv D ⟨j, i⟩`, with `splitCut_lt_iff`
  (lexicographic order) and the two monotonicity consequences
  `flattenOuter_le_of_not_lt`, `le_flattenOuter_of_lt`.
- `splitIndex D j i k : Fin (B.length + 1)`. Its value is the outer block of `k`,
  plus one if `k` lies after the cut. `splitIndex_val_of_lt` and
  `splitIndex_val_of_not_lt` give the two cases; `splitIndex_monotone` and
  `splitIndex_surjective` (the latter needs `hi`, for the label `j + 1`) hold.
- `splitShape D j i hi : BlockShape n`, of length `B.length + 1`. Block `l` has
  size `∑ k with splitIndex k = l, (B.flatten D).size k`. Surjectivity makes
  the sizes positive, and their total is `n` by `Finset.sum_fiberwise`. This is
  `B` with block `j` cut into the inner blocks up to `i` and the rest.
- `splitMerge j : Fin (B.length + 1) → Fin B.length` sends `l` to `l` if
  `l ≤ j` and to `l - 1` otherwise. It is monotone and surjective
  (`splitMerge_monotone`, `splitMerge_surjective`), and
  `splitMerge j ∘ splitIndex D j i = flattenOuter D` (`splitMerge_splitIndex`,
  `splitMerge_comp_splitIndex`, `splitMerge_comp_comp_splitIndex`).
- `size_eq_sum_splitMerge`: the blocks of `splitShape` over `j'` have total size
  `B.size j'`. So `B` is a consecutive coarsening of the split shape. The proof
  regroups the flattened sizes over `j'` (Library
  `size_eq_sum_flattenOuter`) along the fibres of `splitIndex`.
- `splitShape_blockScalar`: `(splitShape).blockScalar K (a ∘ splitMerge j) =
  B.blockScalar K a` over any commutative ring (Library
  `leviEmbedding_blockScalarLevi_coarsen`).
- `standard_splitShape_refines`: the standard pair of the split shape refines
  the standard pair of `B`. The parabolic inclusion is the Library's
  `glBlockCoarseningSubgroups`, and the split-component inclusion is
  `splitShape_blockScalar`.
- `standard_splitShape_strictlyRefines`: over a field with an element other
  than `0` and `1`, the refinement is strict. The reverse refinement would
  include split components and bound the block lengths
  (`ConjugatePairRefinementRankProof.length_le_of_splitComponent_le`), but the
  split shape has one more block than `B`.
- `splitLabel`, `splitMergeLabel`: the same two maps, with the split shape's
  own label type `Fin (splitShape).length`. They come with the monotonicity,
  size and composition lemmas, so that later rewriting does not mix the two
  defeq index types.
