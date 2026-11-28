# The gallery round-trip product at one parameter

For a system `p` of continued compact standard operators between gallery
vertices with a common Levi, `gallery_roundTrip_point_product` works at one
parameter `z`. Write `J(v, w)` for the operator with source `v` and target
`w`. Assume `z` is regular for every ordered pair among `θ`, `θ.opposite`,
`x`, `x.opposite` and `y`, and the representations induced at `x` and `y`
are irreducible. The lemma takes a scalar identity `hθ` for the round trip
starting at `θ` and the four-scalar product law `hprod` with fixed coefficient
`t` in the form of `exists_gallery_roundTrip_product`.

The round trips `J(x.opposite, x) J(x, x.opposite)`,
`J(x.opposite, y) J(y, x.opposite)` and `J(x, y) J(y, x)` are then scalar
(`compactContinuationValue_roundTrip_isScalar`). The operator `J(y, x)` is
surjective (`continuedPair_operator_bijective_of_irreducible`,
`forward_bijective_iff_compact`). The three scalar identities together
with `hθ` and surjectivity allow `hprod` to give `so · si = t · sθ` for the
scalars of the outer and inner round trips and the round trip at `θ`.

The scalar round trips are `j` of Waldspurger IV.3, printed p. 285, and the
product is an instance of IV.3(4), printed pp. 286–287 (source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).
