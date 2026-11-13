# Canonical pushforward comparison on relative cohomology

This internal helper takes cohomology of the published
`pushforwardSingleDerivedSectionsComparison`. For an arbitrary morphism
`f : Y → X` over an affine base, its map goes from cohomology of `f_* N`
on `X` to cohomology of `N` on `Y`. It is natural in `N` and respects
composition with the actual pushforward composition isomorphism.

The published canonical pullback factors as cohomology of the adjunction
unit followed by this comparison. With a coefficient map `a : f^* M → N`,
it is cohomology of the adjoint of `a` followed by the same comparison.
The proof uses the published derived factorization, naturality of the
derived comparison and the specified homology isomorphisms.

For a closed immersion the comparison is an isomorphism, for every
module and degree. Pushforward is exact for a closed immersion. It
therefore preserves the quasi-isomorphism from a module to an injective
resolution. On that resolution, pushforwards of injectives are acyclic
for relative sections, so the derived comparison is invertible.
Naturality transfers invertibility to the module in degree zero, and
taking homology gives the asserted cohomology isomorphism.

All these results concern a fixed affine base. Comparing them with
restriction of scalars after a change of the base ring and proving
naturality of the elementary ideal-sheaf presentation remain separate
obligations.

Authored by Worker 210.
