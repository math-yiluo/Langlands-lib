# Inverse images and the maximality argument for radical quotients

This is internal derived infrastructure for the represented ground-field radical
quotient problem. It uses the published actual group schemes, subgroup functors,
kernels and radical predicate without changing them.

`SubgroupPreimage.groupScheme q j` is the actual pullback of group-scheme
homomorphisms `q : G ⟶ Q` and `j : H ⟶ Q`. Its two projections retain the
pullback property both for schemes over the base and for underlying schemes.
`range_inclusion` identifies its image in `G` with the preimage of the range of
`j` on every relative scheme test. Normality and closedness therefore pull back.
Flatness, surjectivity and smoothness of the projection to `H` follow from
scheme base change. A smooth quotient and smooth `H` give a smooth inverse
image; a closed `H` and affine `G` give an affine inverse image.

`range_eq_bot_of_range_inclusion_le_kernel` proves a useful all-test vanishing
criterion. If the entire inverse image lies in the full scheme kernel of a flat
surjective `q`, its projection to `H` is a flat surjective scheme map and hence
an epimorphism. The pullback identity then implies that `j` is the identity-valued
map, so its image subgroup functor is bottom. This requires no surjectivity on
rational points or on the point group of an original test scheme.

`IsUnipotentRadical.hasTrivialUnipotentRadical_of_preimages` applies the supplied
radical's greatestness to these actual inverse images. Its hypotheses explicitly
require smoothness, connectedness and unipotence of the inverse image of each
smooth connected unipotent normal closed subgroup of `Q`. Greatestness places
that inverse image inside the radical; the specified kernel equality and the
vanishing criterion finish the argument. This is a conditional reduction, not
a proof of unipotent extension closure or of the full radical quotient statement.
Those inverse-image properties and affineness of `Q` remain consumer obligations.

The mathematical route is the ordinary inverse-image and maximality argument
underlying the quotient assertion in Conrad--Gabber--Prasad, *Pseudo-reductive
groups*, second edition (2015), Remark 1.1.4, printed page 5 (PDF page 31).
The module proves the stated formal reductions and base-change properties; it
does not quote the full quotient assertion as an available theorem.

The inverse-image object and projections abbreviate `subgroupIntersection`,
`subgroupIntersectionFst`, and `subgroupIntersectionSnd`. The two pullback
identities reuse the corresponding existing intersection lemmas.
