# Uniqueness of minimal block Weyl representatives

Author: Worker 175.

`Langlands.Geometric.weylMinimalRepresentativeUniqueness` proves the published
closed proposition `Langlands.Geometric.WeylMinimalRepresentativeUniquenessTheorem`.

`weylDoubleCoset_injective` proves that the actual map from
`MinimalRepresentatives B C` to `W_C \ S_n / W_B` is injective for every natural
rank and every pair of positive ordered block shapes. Minimality retains both
conditions from `WeylDefinitions`: the permutation is strictly increasing within
each source block, and its inverse is strictly increasing within each target
block. The proof also covers rank zero. It does not establish existence of a
minimal representative or bijectivity.

This is an internal finite-order proof of the all-rank uniqueness target. For
positive rank, it proves the uniqueness component of the published
`WeylMinimalRepresentativeTheorem`. It uses the actual consecutive
block coordinates and block-preserving Weyl subgroups from the published
`Langlands.Representation.Geometric.WeylDefinitions` pair without modification.
It does not use the Coxeter-group argument mentioned in the original
`WeylStatement` documentation.

## Implemented proof

The coordinate identity `blockIndex_index` is shared from `WeylDefinitions`.
Together with `exists_index_of_blockIndex_eq` and `blockIndex_monotone`, it
identifies block fibers. The ordering argument reuses
`GeneralLinear.BlockShape.index_lt_index_of_block_lt` from
`Group/GL/TriangularParabolic`, whose prefix-sum proof shows that coordinates of
earlier blocks precede those of later blocks. The former local copy named
`block_index_lt_of_lt` is replaced by that same shared result.

Equality of double cosets supplies permutations `c` in the target block Weyl
subgroup and `b` in the source block Weyl subgroup with `v = c * w * b`, using
Mathlib's `DoubleCoset.eq`. Restricting `b` to each source block gives a finite
permutation of that block. Applying `blockIndex C` removes `c`. The target-block
labels of `w` and `v` on the source block are therefore permutations of the same
tuple. Both tuples are monotone, by source-block strict monotonicity and
monotonicity of `blockIndex C`. Mathlib's `Tuple.unique_monotone` makes the two
tuples equal, hence the target-block labels agree at every source coordinate.

This label equality implies that the inverse maps of `w` and `v`, restricted
to any one target block, have the same range. Both inverse restrictions are
strictly increasing. Mathlib's `StrictMono.eq_of_range_eq` then identifies the
restrictions. Surjectivity of the target coordinate equivalence gives equality
of the inverses everywhere, hence equality of the permutations and of their
minimal-representative subtypes.

Finally, `weylMinimalRepresentativeUniqueness` introduces the natural rank and
the two block shapes from the published closed proposition, then applies
`weylDoubleCoset_injective`. No positive-rank hypothesis or separate rank-zero
case is needed.
