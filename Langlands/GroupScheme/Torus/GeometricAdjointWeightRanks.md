# Locally constant dimensions of actual geometric-fibre adjoint weights

For a smooth affine group scheme `G` over `Spec r` and an actual
homomorphism from a coordinate split torus into `G`, this file proves
simultaneous local constancy of all character weight dimensions on
the actual chosen geometric fibres. The commutative ring `r` is
arbitrary. The group fibres may be disconnected, and the torus
homomorphism need not be injective.

`geometricFiberHom` is the actual torus homomorphism in the actual
pullback along `geometricPoint`. It uses the inverse of the
canonical split-torus base-change isomorphism, followed by base
change of the given homomorphism. The definition
`geometricExponentWeightRankProfile` records the finite dimensions
of its existing all-test character weight spaces. The characters
are indexed by the integral-coordinate inverse of
`characterLatticeEquiv` over the chosen algebraic closure of the
actual residue field.

For every specified field-valued point induced by a coefficient
map, the actual weight-summand base-change equivalence identifies
the weight-space dimension with the dimension of the tensor
extension of the relative actual weight module. Mathlib's
`Module.rankAtStalk_baseChange` identifies this with the relative
rank at the image point.

The geometric-fibre comparison applies this result to the actual
chosen geometric point. Fullness of `Spec` supplies its coefficient
map; the resulting base-change morphism equals the original
geometric point. Its image is the original prime by
`Scheme.fromSpecResidueField_apply`. The existing exact field
exponent/character weight-space comparison then proves equality
of the geometric profile with the actual relative rank profile.
The latter is locally constant by
`RelativeAdjointWeightRanks`, giving the stated simultaneous
local constancy on one neighbourhood.

The provenance is internal: it combines the actual relative
weight decomposition, finite projectivity, scheme-base-change
weight equivalences and Mathlib's stalk-rank formulas. It assumes
no relative model beyond the given actual torus homomorphism.
Construction of such a local torus from a fibre torus and the
centralizer/rank-one argument for reductive-locus openness remain
separate structural obligations.
