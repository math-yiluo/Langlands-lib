# Actual imaginary quadratic projectors on module sheaves

This internal construction works on an arbitrary scheme `S`, with an actual
module sheaf `M` and a unital imaginary-field action `rho : L → End(M)`.
Here `L` is an imaginary quadratic CM number field contained in a
characteristic-zero field `K`. The global regular-function ring has a
specified `K`-algebra structure and compatible rational scalars. No
reducedness, flatness, finiteness or nonemptiness assumption is imposed.

The module extends the given action to the actual tensor algebra of global
regular functions by its universal property, using the existing algebra
structure on sheaf endomorphisms given by scalar multiplication. The pure
tensor formula is `r ⊗ t ↦ r rho(t)`. The two previously constructed
coordinate idempotents therefore give actual endomorphisms of the sheaf.
Their idempotence, orthogonality and sum-to-identity follow by applying
the ring homomorphism to those identities in the tensor algebra.

The character identity for each coordinate idempotent proves that its
projector image satisfies every scalar eigen equation on every open.
Tensor induction proves that a tensor element acts on any eigensection
by its selected coordinate scalar, restricted to that open. Thus the
corresponding projector fixes every eigensection and the other projector
kills it.

`sheafEigenProjection` is an actual morphism to the existing full scalar
eigensubsheaf. Its restriction compatibility comes from naturality of
the actual projector endomorphism, and its linearity from module-sheaf
linearity. Composition with the inclusion recovers the projector.
The reverse composite is the identity and the cross composite is zero.
`sheafEigenIso` constructs an actual isomorphism from `M` to the product
of its natural and conjugate eigensubsheaves, in that order. Its forward
map is the pair of projections and its inverse adds the included sections.
The complementary-projector equations prove both inverse laws.

These are derived constructions from the actual field action and structural
scalars; no projector, output eigensheaf comparison or splitting is assumed.
This module does not yet construct a sheaf tensor factor, prove prescribed
geometric ranks or identify a source compatibility condition.
