# Lifting an adjacent two-block swap along a uniform shape

Author: Worker 1032.

This internal helper is derived from the published regrouping theorem
`Langlands.Parabolic.orderedProductRegrouping` and the adjacent merge shapes of
`Group.GL.AdjacentMergeShape`. It makes no literature assertion and assumes no
irreducibility, linkage or commutation result. It is the family version of the
datum-level lifting in `Classification.AdjacentSegmentSwapLifting`: that module
works with segment-product data whose carriers live in `Type (max uF uV)`, while
the juxtaposed proof needs families of representations of `GL_r` with carriers
in `Type uV`.

Throughout, `r > 0`, `BlockShape.uniform N r hr` is the uniform shape
`(r, …, r)` with `N` blocks, `σ : Fin N → SmoothRep (GL_r)` is a family, and
`T.normalizedProductInductionFunctor B` is normalized parabolic induction along
a shape `B`.

## Results

- `merged_swap`: a shape with `L` blocks of size `r` and total `n₀` is, once
  `L = 2` is substituted (which forces `n₀ = 2 * r`), definitionally
  `uniform 2 r hr`. So an isomorphism `i(![σa, σb]) ≅ i(![σb, σa])` along
  `uniform 2 r hr` gives the same isomorphism for any two families `τ`, `τ'` over
  such a shape whose entries at positions `0` and `1` are `σa, σb` and `σb, σa`.
- `uniform_regroup`: for `j + 1 < N`, the product of `σ` along the uniform shape
  is isomorphic to the outer product, along the shape merging blocks `j` and
  `j + 1`, of the inner products of `σ` over the fibers of that merge. This is
  `orderedProductRegrouping` for the data `adjacentMerge`, `adjacentRefinement`,
  `adjacentBlockEquiv` and `adjacent_index` of the uniform shape.
- `uniform_adjacentSwap`: given an isomorphism
  `i(![σ j, σ (j+1)]) ≅ i(![σ (j+1), σ j])` along `uniform 2 r hr`, the products
  of `σ` and of `σ ∘ (j j+1)` along the uniform shape are isomorphic.

## Proof of `uniform_adjacentSwap`

Both products are regrouped with `uniform_regroup`. The transposition
`(j j+1)` does not change the uniform shape, so both regroupings use the same
merged shape and the same fibers, and it suffices to give a fiberwise isomorphism
of the inner products (`Pi.isoMk` and `Functor.mapIso` of the outer induction).
By `adjacentBlockEquiv_val`, the label of position `k` in fiber `m` is
`m + k`, plus one when `j < m`.

- At an outer block `m ≠ j`, the fiber has length one
  (`adjacentRefinement_length_of_ne`) and its label is neither `j` nor `j + 1`,
  so the transposition fixes it and the two inner families are equal.
- At the merged block `m = j`, the fiber has length two
  (`adjacentRefinement_length_merged`), with labels `j` and `j + 1`. The inner
  families are `σ j, σ (j+1)` and `σ (j+1), σ j`, and `merged_swap` applies the
  hypothesis.
