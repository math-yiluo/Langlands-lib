# Full Weyl images and containment of normalizer points

This is internal derived content, uniform in universe `u`. It uses the
map `normalizerPointsMap` and its compatibility with the full
character action, the split-torus identification of the action kernel with
the centralizer, and finiteness of the full Weyl image for a closed split
torus in an affine algebraic group.

For a commutative group scheme `T` over any scheme `S` and homomorphisms
`i : T → H` and `f : H → G`, with both torus maps monic on schemes,
`weylImage_le_postcomp` includes the full character image in `H` into the
full character image in `G`. It sends actual normalizer points along `f`
and preserves their entire character action. Without the monomorphism
hypotheses, all-test containment of the centralizer in the image of `f`
still gives the corresponding containment of base points.

If `T` is split, the two character images are equal, and the centralizing
base points in `G` lie in the image of `H`, then
`normalizerPoints_le_range_of_weylImage_eq` proves the same containment
for all normalizing base points. Given a normalizer point `n` in `G`,
image equality supplies a normalizer point `m` in `H` with the same
character action. The quotient `n * f(m)⁻¹` lies in the action kernel,
which is the centralizer. Multiplying its image containment by that of
`f(m)` gives the claimed containment of `n`.

Over a field, `IsSplitTorus.natCard_weylImage` identifies the order of the
full character image with that of the actual normalizer modulo
centralizer quotient, by the quotient-by-kernel isomorphism. If the ambient
image is finite, a reverse inequality between the two quotient orders
forces equality of the nested character-image subgroups.
`weylImagePostcompEquivOfNatCardLe` is the resulting multiplicative
equivalence between these actual images; its value in the ambient
character-automorphism group is unchanged, as recorded by the `_val`
lemma.

Finally, for a closed split torus in an affine locally finite type ambient
group over a field, the Library finiteness theorem supplies the required
finite image. Thus `normalizerPoints_le_range_of_natCard_le` derives
normalizer containment from the reverse quotient-order bound and all-test
centralizer containment. The subgroup map need not be open or closed.
This module retains the order and centralizer premises; it does not assert
them for a family or prove reductive-monomorphism closedness.
