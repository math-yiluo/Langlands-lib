# A compatible affine cover for integral pinching

This internal construction completes the affine-neighborhood side of the
global integral-pushout argument. It uses the compatible affine pairs of
`IntegralSchemePushoutCompatibleOpens` and the affine basis of a scheme.

`CompatibleAffinePairs i j` is the type of all pairs of affine opens
`U` of `X` and `V` of `Y` such that `i⁻¹(U) = j⁻¹(V)`. The projections
`left` and `right` retain the affine-open proofs, and `compatible` gives
the inverse-image equality.

Under a closed immersion `i`, an integral map `j`, and the displayed
fibre-affine-neighborhood hypothesis, these pairs cover both schemes.
`compatibleAffinePairs_cover_right` applies the existing neighborhood
lemma at each point of `Y`. To prove `compatibleAffinePairs_cover_left`,
a point of `X` in the image of `i` lies in the left open of a pair chosen
at its image under `j`, by the inverse-image equality. The complement of
the image of a closed immersion is open. A point in that complement
has an affine neighborhood inside it; pairing this neighborhood with
the empty affine open of `Y` gives a compatible pair, since both
inverse images are empty.

`integralCompatibleAffineCoverLeft` and
`integralCompatibleAffineCoverRight` package the two covering families
as actual scheme open covers with the same compatible-pair index.
Their members are the corresponding open subschemes, with the canonical
open immersions. Each is affine by construction of the index. This unit
supplies covers and inverse-image equalities; the global scheme, its
universal properties, and the properties of its two maps require the
separate gluing construction.
