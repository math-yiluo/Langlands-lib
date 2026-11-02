# Galois orbit sums of cocharacters

Worker 1272.

This is an internal construction for the averaging step in the proof of
Milne, *Algebraic Groups* (2017), Theorem 25.1, printed page 544 (PDF page
560). It uses the published character and cocharacter lattices, pairing,
and Galois representations in `Torus.Lattice` and `Torus.LatticeGalois`.

`latticePairing_transport` proves that simultaneous transport of a
character and a cocharacter along an endomorphism of the extension base
preserves the pairing. On points, the transported composite is evaluated
on the same unit, read with the changed base structure. Every endomorphism
of the multiplicative group over a domain is an integer power map, so
changing the base structure does not change its exponent.
`latticePairing_galoisRepresentation` applies this to the published
Galois actions; `latticePairing_galoisRepresentation_right` moves an action
on the cocharacter to the inverse action on the character.

`CocharacterAveraging.orbitSum ρ ν` is the sum of all translates of `ν`
under a representation of a finite group on a module over the integers.
It is fixed by the group, by reindexing the sum by left multiplication.
For an integer-valued additive functional whose nonnegative half-space
contains either every translate of `ν` or none of them,
`nonneg_orbitSum_iff` says that the orbit sum belongs to that half-space
exactly when `ν` does. If all terms are nonnegative their sum is
nonnegative; otherwise all terms are strictly negative, and the group
contains the identity, so their sum is strictly negative.

`galoisOrbitSum` specializes this construction to the actual cocharacter
lattice of a commutative group scheme after base change.
`galoisOrbitSum_fixed` proves invariance under every algebra automorphism.
`galoisOrbitSum_nonneg_iff` preserves the nonnegative pairings with a
Galois-stable set `Φ` of characters, assuming that its subset cut out by
nonnegative pairing with `ν` is Galois-stable as well. This is the finite
root-cone argument used in Milne's proof, with the geometric hypotheses
kept explicit.

The construction uses an integral sum, so it introduces no division by
the extension degree and no restriction on field characteristic. In fact
the Lean construction only requires commutative base rings, an extension
ring that is a domain, and a finite type of algebra automorphisms. It does
not assert that Galois-fixed cocharacters descend to the original field,
that a torus admits a finite Galois splitting field, that an actual root
set or a parabolic root subset is stable, or that equal root subsets give
equal subgroup functors. Those geometric steps remain separate
prerequisites of `ParabolicDynamicStatement`.
