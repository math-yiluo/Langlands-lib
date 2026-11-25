# Finite morphisms and closed immersions detected on split torus characters

Internal helper for the proof of
`Langlands.GroupScheme.TorusAnisotropicPartStatement`.

The defined type `characterLattice.pullbackCokernel f` is the quotient of the
source character group by the image of pullback along `f`. Its finiteness is
the cokernel hypothesis in the final morphism criterion.

For an injective homomorphism `g : Λ' → Λ` with finite cokernel, this module
imports and reuses `Diagonalizable.finite_mapDomainRingHom` from the published
`Rational/SplitTorusIsogenyOfLatticeMapsProof`. That lemma uses the coset
coordinate map to present the group algebra of `Λ` as a finite free module
over the group algebra of `Λ'`. Taking spectra proves that the restriction
morphism of diagonalizable groups is finite.

The final finiteness lemma transports this result through the canonical diagonalizable
models of actual split tori. These models identify a group homomorphism with
restriction along its actual character pullback.

The same canonical models identify surjective character pullback with a closed
immersion. This uses the published closed-immersion criterion for restriction
maps of diagonalizable groups, which follows from surjectivity on the group
algebras. Both conclusions concern the underlying morphism of schemes.
