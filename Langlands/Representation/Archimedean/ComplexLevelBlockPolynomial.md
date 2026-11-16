# Level products are polynomial along a root subgroup

Let `i, r : Fin n` with `r = i + 1` and `rootMatrix i r z = 1 + z E_{r,i}`.

## Results

- `tailRows_mul_of_zero`: if `b` has no entries from rows `≥ m` to columns `< m`, the rows
  `m, …` of `b y` are the corresponding block of `b` times the rows `m, …` of `y`.
- `rootMatrix_zero_of_ne`, `det_rootMatrix_submatrix`: for `m ≠ r` the root matrix satisfies
  this condition and its block on the rows `m, …` has determinant `1`.
- `levelDet_rootMatrix_mul`, `gramMinor_rootMatrix_mul`: hence for `m ≠ r` the level
  determinants and the Gram determinant of level `m` are invariant under
  `y ↦ rootMatrix i r z · y`.
- `levelDet_rootMatrix_mul_affine`: at the level `r`, `levelDet r A (rootMatrix i r z · y)` is
  affine in `z` (only the first row `r` of the block changes, by `z` times row `i`).
- `prod_affine_mem`, `prod_conj_affine_mul_mem`: products of `h` affine factors and `b`
  conjugate affine factors lie in `bidegLT (h + 1) (b + 1)` (multiplied onto an element).
- `isBlockPoly_levelProduct`: if the Gram exponent of the level `r` vanishes,
  `dτ_r - (h_r + b_r)/2 = 0`, and `h_r < p`, `b_r < q`, then every level product is
  block-polynomial of bidegree `< (p, q)` for the root `(r, i)`: the other level factors are
  constant in `z` and the level-`r` factor is a product of `h_r` affine and `b_r` conjugate
  affine functions.
- `isBlockPoly_of_mem_levelSpan`: the same for every element of `levelSpan h b dτ`.

## Provenance

Internal infrastructure of Task 7064 for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
