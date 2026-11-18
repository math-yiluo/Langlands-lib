# Closed normalizers of multiplicative-type subgroups

`Langlands.GroupScheme.relativeTorusClosedNormalizerModel` gives an actual
closed subgroup scheme of the ambient group representing the torus
normalizer on every relative test scheme. The base and ambient group scheme
are arbitrary. The input is a closed inclusion of a relative torus.

`normalizer_range_isClosedRepresentable_of_multiplicativeType` gives the same
existence conclusion for a closed inclusion of any relative multiplicative-type
subgroup. The affine-base lemma applies to a closed subgroup with affine flat
structure morphism and fpqc-projective coordinate module.

Over an affine base, pull the closed subgroup back along the inverse-conjugation
map from the product of the subgroup with the ambient group. The published
closed-factorization construction represents the points whose whole conjugation
family factors through the subgroup. Intersect this locus with its inverse
under group inversion. A point factors through the intersection exactly when
conjugation in both directions preserves the subgroup after every refinement
of the test scheme. The transfer from scheme representability to group-scheme
representability gives the actual closed normalizer. For diagonalizable
subgroups the group algebra is free, so the affine-base hypotheses hold.
The proof then descends along affine open covers and the fppf cover that
makes the subgroup diagonalizable.

The construction composes the Library's universal closed-factorization locus,
conjugation-into condition, diagonalizable projective coordinates, and fppf
closed-subgroup descent. It supplies the closed representative used in the
Weyl-affineness route. Smoothness of its structure morphism requires a
separate argument.
