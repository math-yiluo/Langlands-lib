# Rank-one normalization over an arbitrary local ring

`localSplitRankOneNormal` proves the unchanged published
`LocalSplitRankOneNormalStatement` in every universe.

For a simple root, the root at its reflection index is its negative.
The given maps are therefore an actual opposite root pair. Apply
`localSplitRootPairLaws` to these maps and their given Weyl reflection.
Its first two clauses give both conjugation identities on every affine
scheme test. Its third clause at the base test gives the Weyl square
equal to the coroot at minus one, since the constant point at the base
is the original point.

This is an internal specialization of the all-test supplied-root laws.
It imposes no condition on the commutative local ring beyond those of
the target: nilpotents and arbitrary characteristic are retained.
