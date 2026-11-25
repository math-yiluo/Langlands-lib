# The prescribed torus map for an affine split root-datum isogeny

This internal construction supplies the torus homomorphism prescribed by the
unchanged `AffineSplitIsogenyTheoremStatement`. It does not construct a
homomorphism of the ambient reductive groups.

For reduced root data `P` and `Q` on the finite coordinate lattices `ℤ^I` and
`ℤ^{I'}`, and `f : RootDatumIsogeny p Q P`,
`AffineRootDatumIsogeny.torusMap S f` is the existing integral-coordinate torus
homomorphism `splitTorus.exponentHom S I I' f.weightMap`, viewed in the category
of group schemes. It is defined for every base scheme `S`.

`points_torusMap` proves precisely the monomial character identity on all test
schemes. `card_eq` uses the injective weight and coweight maps to obtain the two
opposite rank inequalities over `ℤ`. Equal ranks and injectivity give the finite
cokernel theorem `finite_weightMap_cokernel`. Over every commutative ring `R`,
including the zero ring, `isIsogeny_torusMap` then applies
[`Torus.ExponentIsogenies`](../Torus/ExponentIsogenies.md) to prove that this
torus map is finite, flat and surjective.

The provenance is internal: this is the direct specialization of the published
`RootDatumIsogeny` weight map to the published `splitTorus.exponentHom`, together
with the arbitrary-ring isogeny theorem in the supporting module. No root-group,
pinning, or ambient realization assertion is used. The characteristic condition
on `p` in the affine isogeny theorem is unnecessary for this torus construction.
