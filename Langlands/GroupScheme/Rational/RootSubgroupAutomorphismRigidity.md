# Scalar linearity for root automorphisms

Worker 1368. This internal construction uses the Library's represented-root,
natural vector-coordinate and unique-weight-scalar interfaces.

Precomposing weight coordinates with an actual equivariant automorphism gives
another coordinate system of the same weight. For a nonzero weight of a split
torus, the published coordinate-scalar uniqueness theorem identifies these
scalar structures, forcing the automorphism to be scalar-linear on every test.

An endomorphism fixing a torus preserves each actual root functor, so its
composite with a representing inclusion factors uniquely through that
inclusion. The construction `rootHomOfFixesTorus` records this restricted
homomorphism and its exact ambient composition equation. The inverse of a
torus-fixing automorphism also fixes the torus; restricting both maps gives
`rootIsoOfFixesTorus`. Cancellation along the representing monomorphism proves
the two inverse identities.

The induced root automorphism commutes with the full original torus action.
After the representing inclusion, that assertion is preservation of
conjugation by the torus-fixing ambient automorphism; monicity reflects it.
For a field, the final theorem assumes actual weight coordinates on the
represented root and identity of the ambient differential on the root's
actual tangent image. Cancellation along the representing inclusion makes
the induced root automorphism's differential the identity. Scalar linearity
and the vector-endomorphism rigidity theorem then make the induced root
map the identity. Its composition equation puts the entire root functor
in the ambient automorphism's fixed subgroup.

All constructions retain arbitrary scheme tests and use no characteristic
restriction. Weight-coordinate existence and the stated differential-image
identity remain explicit premises.
