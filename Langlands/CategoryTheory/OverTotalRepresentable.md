# Representing total presheaves and transporting representations

These are internal categorical constructions for the actual Picard arrow
scheme. They use the published total presheaf of a slice presheaf and
Mathlib's `RepresentableBy` data and equivalence adjunction.

`RepresentableBy.toOverTotal` takes a representation of a presheaf on
`Over S` by `A : Over S` to a representation of its total presheaf by
`A.left`. A morphism to `A.left` gives its composite to `S` and the
corresponding slice-presheaf section. The inverse retains the underlying
morphism of the inverse slice representation. The inverse and naturality
proofs use the slice commutative triangles and representation naturality.

`RepresentableBy.ofEquivalence` transports a representation of a presheaf
precomposed with an equivalence of test categories to a representation of
the original presheaf. Its pointwise equivalence uses the inverse
adjunction, the supplied representation, and the counit comparison. The
naturality proof is the counit naturality square followed by presheaf
functoriality. Neither construction asserts any geometric representability
without its stated representation data.
