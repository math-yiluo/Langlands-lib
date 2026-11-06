# The ordinary Galois permutation of actual root indices

This internal construction gives the ordinary Galois action on the indices of
any supplied actual root datum for a descended torus map. The field extension
is arbitrary; finiteness, the Galois extension property, and reductivity are not
needed for this construction. The base fields and group schemes have universe
`u`, and the supplied root index type has an independent universe `v`.

`characterLattice.galoisEquiv` and `cocharacterLattice.galoisEquiv` package the
published ordinary representations as integral linear equivalences. Their
inverse is the representation of the inverse field automorphism.

`mem_roots_galois_iff` uses the published actual adjoint-weight transport
`RelativeRoot.weightSpace_galois_ne_bot_iff`. An actual root is precisely a
nonzero character with a nonzero actual weight space. Invertibility preserves
the first condition, and the weight-space theorem preserves the second,
including the defining tests over all coefficient algebras.

`IsRootDatumOf.galoisRootIndexEquiv` identifies the indices with the range of
the root embedding, restricts the ordinary character action to that range,
and returns to the original indices. Its root formula identifies the resulting
root exactly with the ordinary Galois transform of the original root.
`IsRootDatumOf.galoisRootIndexAction` proves the identity and multiplication
laws by root injectivity and the published representation laws.

The last lemma states that the permutation preserves those roots that are roots
for any other descended map from the same torus to an affine group scheme. This
can be applied to a descended Levi inclusion. It is a statement about the
actual adjoint root sets.

The provenance is an internal combination of the published actual root-datum
predicate, ordinary lattice representations, and all-test adjoint-weight
Galois transport. No root base is chosen here. Coroot transport and a Weyl
correction preserving a chosen base remain separate obligations.
