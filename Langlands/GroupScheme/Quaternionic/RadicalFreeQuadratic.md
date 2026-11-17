# Quadratic forms with zero quadratic radical

Author: Worker 177.

This internal development weakens the invertible-polar-matrix hypothesis in
the published hyperbolic-pair construction and local scalar dimension bound.
It applies to actual Tits quadratic forms, defined as the quotient of the
matrix space by the alternating matrices for a first-kind involution.

`IsRadicalFreeQuadratic q` says that a vector whose quadratic value is zero
and whose polar pairing with every vector is zero must itself be zero.
For the scalar involution, this is the vanishing of the ordinary quadratic
radical. It allows a nonzero radical of the polar bilinear form in
characteristic two. No bound on that polar radical is built into the
definition. An invertible polar matrix implies this property, as proved
in `IsNondegenerateQuadratic.isRadicalFree`.

For any first-kind involution of a division algebra and any finite index
type, a nonzero singular vector in a form with this property has a nonzero
polar row. Choosing a nonzero entry and scaling a coordinate vector gives
a vector with polar pairing one. Subtracting a multiple of the original
singular vector makes the partner singular without changing that pairing.
The existing positive-Witt-index theorem supplies the starting singular
vector. Thus a positive Witt index gives an actual hyperbolic pair without
assuming invertibility of the entire polar matrix. These constructions
retain every field characteristic and all displayed universe parameters.

`scalar_card_le_six_of_radicalFree_of_quadraticWittIndex_one` specializes
to ordinary scalar quadratic forms over any nonarchimedean local field.
The two polar functionals of a hyperbolic pair define a linear map to
`K × K`. The restriction of the actual quadratic form to its kernel is
anisotropic: a nonzero singular vector there would span a two-dimensional
totally singular subspace together with the first hyperbolic vector,
contradicting Witt index one. The published local anisotropic quadratic
dimension bound gives kernel dimension at most four. Rank-nullity and the
two-dimensional target give total dimension at most six.

The final corollary excludes Witt index one in every dimension at least
seven. In particular it applies in odd dimension in characteristic two;
it does not assume an invertible odd-size alternating polar matrix. No
identification between an arbitrary actual type-B group and one of these
quadratic forms, nor any split-rank comparison for that group, is proved
here. Those geometric inputs remain separate obligations for applying
this bound to the local rank-one Tits-index enumeration.

The provenance is internal composition and extension of the published
`HyperbolicPair`, `WittIndexOneInputs`, `ScalarInvolution`, and local
quadratic anisotropic dimension bound. The Witt index used throughout is
the published supremum of dimensions of totally singular subspaces.
