# Exterior powers of actual matrix representations

This internal construction applies the exterior-power functor to actual
finite matrix representations. The basis of the `d`th exterior power of
the standard rank-`N` module is indexed by the `d`-element subsets of
`Fin N`. Exterior-power functoriality gives a matrix homomorphism in this
basis; matrices arising from invertible input matrices are invertible.

The entry formula is the determinant of the corresponding minor, written
with the tuple orientation of Mathlib's exterior pairing. Because ring
homomorphisms preserve determinants, these matrices commute with every
coefficient-ring map. They therefore define a natural homomorphism of the
actual general linear group functors and an actual group-scheme
homomorphism.

`exteriorGL_basisLine_iff` combines the exterior-line criterion with these
matrix coordinates. For a chosen increasing selection of standard basis
vectors, preservation of their coordinate subspace is equivalent to the
exterior matrix taking the corresponding exterior basis vector to a unit
scalar multiple of itself. This is an equality of actual vectors over any
commutative coefficient ring.

`exteriorRepresentation` composes that homomorphism with a given matrix
representation. The final point-matrix comparison holds for all relative
scheme tests, using the existing corepresented point equivalence. These
constructions are the exterior-representation step in Milne (2017),
Lemma 4.28, with explicit coefficient-ring and group-scheme comparisons.
