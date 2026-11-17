# Galois orbits of weights of actual irreducible representations

This module proves the exact second conjunct of the published
`MultiplicativeTypeRepresentationGaloisOrbitStatement`: the nonzero actual
character spaces of an irreducible representation, after extension to any
separable closure of the original field, are indexed by one orbit of the
actual Galois action on characters.

Coefficientwise conjugation carries a nonzero character vector to a nonzero
vector of the conjugated character. Thus every conjugate of a weight is
a weight. For a chosen weight, sum all the character spaces in its orbit.
This subspace is stable on every affine algebra test, since each character
space is stable. It is also invariant under coefficientwise Galois
conjugation. Effective Galois subspace descent identifies it with the
extension of its original vectors, which form an original stable subspace.
Irreducibility forces this original subspace to be zero or the whole
space; the chosen weight excludes zero. Thus the orbit sum is the whole
extended space.

Independence of the complete character family makes each character space
outside the orbit disjoint from this orbit sum. Since the sum is the
whole space, an outside character space must be zero. This proves the
other containment of the weight set. A weight exists because the
character spaces span a nonzero extended coordinate space.

The general argument applies to any Galois field extension for which
character-space spanning is supplied. For groups of multiplicative type,
the Library splitting theorem and diagonalizable character decomposition
supply that hypothesis over any separable closure. The proof uses no
smoothness or reducedness condition. Its source context is Milne,
*Algebraic Groups* (2017), Theorem 12.30 and proof, printed pp. 241–242;
the implementation uses the Library's infinite Galois subspace descent
rather than choosing a finite Galois splitting field.
