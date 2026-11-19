# The actual odd quadratic presentation in type B

`Langlands.GroupScheme.typeBOddQuadraticPresentation.{u}` proves the
Library proposition `TypeBOddQuadraticPresentationStatement.{u}`. It
uses the actual supplied Cartan entries, the numbering, and simple
connectedness to construct the vector quotient. The absolute simplicity
hypothesis is present in the target. The quotient construction uses the
semisimple pinning already supplied by the Tits-index data.

The quotient is affine and becomes the full split odd norm-one group
over the separable closure. It therefore has a local isomorphism over a
finite Galois extension. The exact isometric conjugators of its Galois
twists give a matrix cocycle, which Hilbert 90 trivializes. The quadratic
class descends by taking the Galois-fixed coefficients of its triangular
representative modulo alternating matrices. The corresponding conjugation
on every relative test descends the group isomorphism to the full actual
norm-one group of this scalar form.

The form becomes the split odd form under the covering-field basis
change. Injective coefficient extension reflects zero quadratic radical,
and rank and nullity give the exact polar-kernel dimension, including
dimension one in characteristic two. The proof reindexes the form and
its norm-one group on `Fin (2 * n + 1)` and composes the actual quotient
map with that isomorphism. The central-isogeny transport theorem retains
finiteness, flatness, surjectivity, local finite presentation and
centrality of the full scheme-theoretic kernel. Central isogenies
preserve split rank, and the scalar norm-one rank theorem identifies
this rank with the quadratic Witt index.

The paired statement records the comparison with Tits's 1966 type-B
description and his 1968 quadratic and scheme-equation conventions. The
proof implements the construction over every field by split root data
and Galois descent.
