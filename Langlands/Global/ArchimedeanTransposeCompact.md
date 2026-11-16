# Transpose inverse and the standard infinite compact

This is internal infrastructure for Task 7294 by Worker 264, derived from the
Library's concrete standard compact subgroup and the already constructed
archimedean smooth transpose pullback. No maximality theorem or
representation-theoretic contragredient identification is used.

For a field `F` in an arbitrary universe and any natural number `n`,
`inverseTranspose_mem_standardInfiniteCompact` proves that transpose inverse
preserves `standardInfiniteCompact F n`. The proof uses the published membership
criterion: at each real place the matrix is orthogonal, and at each complex
place it is unitary. Inversion preserves the compact subgroup because it is a
subgroup, and matrix transpose preserves unitarity. The coordinate identities
for transpose inverse identify the real and complex matrix components with
these transposed inverse matrices.

`compactTranspose F n` restricts transpose inverse to a continuous group
automorphism of the actual standard infinite compact subgroup. Its inverse is
the same map, and the evaluation and involution identities are proved. The
construction of this group map requires no number-field hypothesis.

When `F` is a number field, `compactOrbitSpan_smoothTranspose` proves that the
complex span of the compact orbit of `smoothTranspose f` is exactly the image
under `smoothTranspose` of the compact orbit span of `f`. The proof applies
`Submodule.map_span` and matches orbit elements using right-translation
covariance and the involutive compact automorphism. Restriction of the
smooth-function equivalence therefore gives a linear equivalence of these
orbit spans. `isCompactFinite_smoothTranspose_iff` deduces preservation and
reflection of finite dimensionality of the actual compact orbit span.

These results concern the group and its action on archimedean smooth functions.
They do not construct a full adelic cuspidal realization or establish the
Gelfand–Kazhdan bridge required for Task 7294's final target.
