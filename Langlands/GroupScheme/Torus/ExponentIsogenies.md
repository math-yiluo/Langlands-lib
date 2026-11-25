# Integral-coordinate isogenies over arbitrary affine bases

This is an internal extension of the published diagonalizable-group algebra
and integral-coordinate torus constructions. It supplies the torus part needed
in the affine split isogeny theorem, without constructing an ambient reductive
homomorphism.

For an injective map of abelian character groups with finite cokernel,
`Diagonalizable.isIsogeny_restrictMap` proves that the induced homomorphism
of diagonalizable groups is finite, flat and surjective over every commutative
ring. The ring may be zero. The proof uses the existing linear equivalence
between the group algebra and the free module indexed by the cokernel.
That index type is nonempty, so its free module is faithfully flat even
over a zero coefficient ring. The finite cokernel supplies module finiteness.

For finite coordinate sets `I` and `J`,
`splitTorus.isIsogeny_exponentHom` applies this result to the existing
integral map `splitTorus.exponentHom`. The comparison with the diagonalizable
model is proved on points over every test scheme. The separate theorem
`splitTorus.pointsEquiv_exponentHom` gives the prescribed monomial pullback
identity over any base scheme.

The provenance is the existing Library's group-algebra coset decomposition
(`Torus.DiagonalizableFaithfullyFlat`), finite-cokernel finiteness
(`Rational.SplitTorusIsogenyOfLatticeMapsProof`), and actual integral character
maps (`Torus.ExponentHomomorphisms`). The proof extends their field or nonzero-ring
wrappers without assuming reductivity or a root datum.
