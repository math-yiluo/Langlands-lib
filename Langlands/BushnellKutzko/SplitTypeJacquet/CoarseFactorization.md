# The coarse two-block parabolic of a standard order

Module `Langlands.BushnellKutzko.SplitTypeJacquet.CoarseFactorization`.

## Two-block matrices

For finite index types `T`, `R`, `upperHom` and `lowerHom` are the homomorphisms from the
additive groups of corner matrices to the upper and lower unipotent `2 × 2` block matrices in
`GL (T ⊕ R) F`, and `leviHom` is the block diagonal embedding of `GL T F × GL R F`. Conjugating a
unipotent block matrix by a block diagonal one multiplies the corner on both sides
(`leviHom_conj_upperHom`, `leviHom_conj_lowerHom`); an invertible block diagonal matrix lies in
the range of `leviHom` (`mem_range_leviHom`).

## The coarse decomposition

For a block function `blk : ι → ℕ` and a cut `j`, `Late blk j` are the indices with
`j ≤ blk p` and `Early blk j` the others; `coarseReindex` writes matrices as `2 × 2` block
matrices with the late indices first. `coarseN F blk j` is the subgroup of matrices that become
upper unipotent, that is the identity plus a matrix supported on late rows and early columns;
this corner lies below the block diagonal of `blk`. `coarseM` is the coarse block diagonal
subgroup and `coarseNbar` the opposite corner. `coarseM_le_normalizer`: `coarseM` normalizes
`coarseN`.

`coarse_upper_mem_J1`: an element of `coarseN` whose corner has entries in the maximal ideal
lies in `J1 F blk`; `coarse_lower_mem_J1`: an element of `coarseNbar` with integral corner lies
in `J1 F blk`.

`coarse_factor` (**Iwahori factorization**): every `x ∈ J0 F blk` is `l * m * u` with
`l ∈ J1 ⊓ coarseNbar`, `m ∈ J0 ⊓ coarseM` and `u ∈ J1 ⊓ coarseN`. Proof: write the reindexed
matrix as `[[A, B], [C, D]]`. The corner `B` (late rows, early columns) has entries in the maximal
ideal, so `A A'` is congruent to the identity, where `A'` is the late block of `x⁻¹`; by
`exists_intGL_of_sub_one`, `A` is invertible with integral inverse. The Schur complement
factorization `Matrix.fromBlocks_eq_of_invertible₁₁` gives the three factors, with corners
`C A⁻¹` (integral) and `A⁻¹ B` (in the maximal ideal).
