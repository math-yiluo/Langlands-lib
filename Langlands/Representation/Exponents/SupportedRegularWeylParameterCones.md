# Supported parameters in actual diagonal coordinates

Author: Worker 165. These internal adapters connect the published
`IsPositiveRootParameter`, `positiveRootParameterCone`, and
`positiveRootBlockSums` with the numerical helpers used for the supported
regular Weyl comparison. They assert no representation-theoretic selection
or occurrence theorem.

The weighted lifting step reuses
`Langlands.Exponents.diagonal_cone_of_weighted_block_cone` from
`WeightedBlockCone`. For a block shape with sizes `d_i`, it lifts a closed
cone for `d_i*v_i` to the repeated diagonal vector `v (blockIndex B a)`.
This is the identical statement previously proved here by block-average
duality. The shared implementation retains the existing interpolation proof:
block sums give the total and boundary inequalities, and constancy within
each block gives every interior partial sum. The duplicate lifting declaration
and its private block-average helper were removed during integration.

`closedCone_of_blockwise` reindexes the actual coordinates by the existing
block index equivalence. Zero total and the monotone-test pairing inequality
hold after summing the corresponding facts on each consecutive block.

`closedCone_of_positiveRootParameter` uses the published weighted open cone
in each middle block, weakens it to the closed cone, and applies the two
blockwise and weighted lifting results. The direct fine presentation is reached in
`closedCone_of_transported_positiveRootParameter` through the literal shape
equality; the parameter and coordinate indices are transported together using
the existing `PositiveRootBlockSumsProof.transport_blockIndex`.

`block_pairing_zero` reindexes a diagonal pairing over coarse blocks and
uses its assumed zero sums. `orthogonality_of_positiveRootParameter` supplies
those sums from the third clause of the published `positiveRootBlockSums`.
`antitone_coarseParameter` composes strict decrease of the coarse parameter
with monotonicity of the actual coarse block index.

All statements allow arbitrary real coarse central shifts, rank zero and the
one-block case. Block sizes retain the positivity required by the existing
`BlockShape` definition.
