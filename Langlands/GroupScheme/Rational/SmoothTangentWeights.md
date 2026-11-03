# Intrinsic weight quotients for smooth equivariant homomorphisms

This internal module combines the actual smooth differential theorem in
`Lie.SmoothDifferential` with the split-torus weight decomposition results in
`Rational.SurjectiveTangentWeights`.

Let `q : H ⟶ G` be an actual homomorphism of affine group schemes locally of
finite type over a field `k`, in an arbitrary universe. Suppose a split torus
acts on both groups and `q` intertwines the actions on every test scheme.
The hypothesis on `q` is smoothness of its underlying scheme morphism.

The differential maps each intrinsic character space onto the corresponding
target character space, and its restriction to that space is surjective.
`smoothActionWeightSpaceQuotientEquiv` identifies the target character space
with the source character space modulo the kernel of the restricted
differential. Any absent source character is also absent in the target,
including the zero character. The full weight span for every additive
subsemigroup maps onto the corresponding target span.

Each result applies `Lie.targetMapLinear_surjective_of_smooth` at the
coefficient algebra `k`, then the corresponding theorem for a surjective
equivariant differential. Thus differential surjectivity is proved from
actual scheme smoothness. Scheme surjectivity of `q` is not needed for
these linear conclusions. This module does not assert smoothness or
surjectivity of a morphism between semigroup subgroup representatives.
