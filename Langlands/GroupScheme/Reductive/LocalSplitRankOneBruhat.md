# The rank-one Bruhat relation over an arbitrary local ring

`localSplitRankOneBruhat` proves the unchanged published
`LocalSplitRankOneBruhatStatement` in every universe.

For a simple root, the root at its reflection index is its negative.
Apply `localSplitRootPairLaws` to the two given root parametrizations
and their given Weyl reflection. Its fourth clause, restricted to the
affine test specified by the target, is the required lower-root,
coroot, upper-root factorization with denominator the supplied unit
whose value is one plus the product of the two coordinates.

This is an internal specialization of the all-test supplied-root laws.
It imposes no reducedness, noetherian, henselian or characteristic
restriction on the commutative local ring.
