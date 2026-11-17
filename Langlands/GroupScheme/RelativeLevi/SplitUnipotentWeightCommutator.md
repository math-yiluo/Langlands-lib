# Independent nonnegative weights in a regular contracting group

This derived unit works over any commutative ring, on every scheme test.
Fix an equivariant root family in a split-torus big cell with negative and
positive root lists, and a regular cocharacter `ν` whose pairings have the
specified strict signs. Let `j : U → G` represent its actual dynamic
unipotent subgroup. An independent cocharacter `wt` measures the bounds;
it may vanish on some of the positive roots.

`exists_unipotent_commutator_eq_weight_ge_of_regular` expresses the standard
commutator of two positive root points inside `U` in the original positive
root order. If the two input `wt` pairings are nonnegative, every output
coordinate of `wt` weight less than their sum is zero. The proof applies
`exists_posComm_eq_weight_ge_of_regular` to the reversed, negated inputs.
The commutator identity changes that convention into the standard one.
The existing factored-root formulas give the ambient product identity,
and the monomorphism `j` cancels to prove it in `U`.

`commutator_unipotent_rootFactor_le_of_regular` transfers this statement to
the subgroup commutator bound for any natural weight family equal to the
`wt` pairings. Each surviving ordered factor belongs to the subgroup at
the sum cutoff, and lower-weight factors are the identity. The regular
cocharacter constructs the cell coordinates; the independent cocharacter
controls their weights. No ordered product is rearranged, and the
independent weights need not be strictly positive.

`positiveCellRootHeightChart` builds an explicit root-height chart from this
same supplied cell when `U` is affine. It uses the actual factored positive
root maps, the positive-product scheme isomorphism, and the natural regular
heights obtained by taking the nonnegative integer pairings with `ν`.
`positiveCellRootWeightData` then equips this chart with the natural pairings
with any `wt` nonnegative on the positive list. The second commutator theorem
supplies its required all-test bound. Thus this is actual chart and weight
data constructed from the cell, rather than a weight assignment to an
unrelated chosen chart.

The construction derives from `SplitBorelUnipotentCommutator` and
`LocalSplitWeightSubgroup`. It does not identify the positive-weight
subgroup for `wt` with an arbitrary supplied radical, construct compatible
choices, or descend a filtration.
