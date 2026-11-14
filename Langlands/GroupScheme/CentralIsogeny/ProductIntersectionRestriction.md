# Restricting a central product to a subgroup

For a central homomorphism `z : Z ⟶ G`, a homomorphism `d : D ⟶ G`, and a
monic subgroup presentation `i : P ⟶ G` containing the range of `z`,
`centralProductIntersectionFactor` constructs the multiplication map from
`Z × (D ×_G P)` to `P`. Its composite with `i` is the prescribed central
product homomorphism into `G`.

This is an internal categorical construction for use in the derived-group
correspondence. It uses the published represented-subgroup factorization
construction, the actual scheme-theoretic intersection, and multiplication
of commuting group-scheme homomorphisms. No reductivity, smoothness or
base-field hypothesis is used.

`productIntersectionProjection` keeps the `Z` coordinate and applies the
first intersection projection in the other coordinate.
`centralProductIntersectionFactor_square` proves that the two routes from
the product with the intersection to `G` agree.

`centralProductIntersectionFactor_isPullback` proves that this square is
Cartesian on the underlying schemes over the base. Given compatible
test-scheme points `(a, b)` of `Z × D` and `p` of `P`, factor `z` through
`P` and form the `P` point `z(a)⁻¹ p`. Compatibility says that this point
and `b` have the same image in `G`, so they give a point of `D ×_G P`.
Together with `a` this is the required lift. The first intersection
projection is monic because `i` is monic; it gives uniqueness.

Finally, `isCentralIsogeny_centralProductIntersectionFactor` states that if
the global multiplication `Z × D ⟶ G` is a central isogeny, this restricted
map to `P` is a central isogeny. It applies the general Cartesian-square
stability lemma in the accompanying `CentralIsogeny.Pullback` module.
These results supply factor maps conditional on containment of `z` and
the global central isogeny. They do not prove the torus or parabolic
properties of the intersection.
