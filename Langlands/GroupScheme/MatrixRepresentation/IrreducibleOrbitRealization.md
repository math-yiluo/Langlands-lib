# Irreducible realization of actual geometric character orbits

This module proves the exact third conjunct of the published
`MultiplicativeTypeRepresentationGaloisOrbitStatement`: for every actual
character over any separable closure of the original field, its full
Galois orbit is the weight set of an actual irreducible finite-coordinate
representation over the original field.

The extraction lemma starts with a semisimple original representation,
a specified nonzero geometric character space, and the hypothesis that
geometric character spaces span. The selected-character projector is
nonzero. If it vanished on the extension of every simple original stable
subspace, semisimplicity would make it vanish on every original vector.
Extension-field linearity and spanning by those vectors would then make
it zero everywhere, contradicting its identity action on the specified
nonzero character space. Thus some simple original subspace has a
nonzero image under this projector after extension.

The projector preserves every stable subspace because it is one of the
linear coefficient operators of the universal action. Its image lies
in the selected character space when character spaces span. Choose
actual split coordinates on the resulting simple original subspace.
Scalar extension identifies its image with that extended subspace.
Injectivity of the inclusion reflects the character equation, giving
a nonzero character vector in the actual irreducible subrepresentation.

The Library occurrence theorem supplies an original representation
containing any specified geometric character. Multiplicative-type
semisimplicity and diagonalizable spanning over a separable closure let
us apply the extraction lemma. The single-orbit theorem identifies the
simple representation's weights with an orbit; since the specified
character is in it, shifting the orbit center gives precisely the
requested orbit. The source context is Milne, *Algebraic Groups* (2017),
Theorem 12.30 and proof, printed pp. 241–242. This implementation uses
coefficient occurrence and simple-subspace extraction instead of
constructing the descended orbit representation explicitly.
