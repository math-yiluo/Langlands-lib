# Uniqueness of actual fppf subgroup images

For group schemes over an arbitrary base scheme, a represented subgroup that
contains the ordinary all-test image of a subgroup under a homomorphism also
contains any actual fppf image. Consequently two actual fppf images of the same
subgroup under the same homomorphism agree as subgroup functors.

The convenience lemma `le_of_map_le_of_isRepresentedBy` uses the published
`IsFppfImage.le_of_map_le` from `SubgroupFunctor.FppfProductImage`. A representing
monomorphism makes subgroup membership fppf-local, so that theorem applies.
Applying this containment in both directions gives uniqueness. The published
minimality proof obtains a lift after pulling back the actual image projection
and descends membership along that cover.

This is an internal derived consequence of the Library definition
`SubgroupFunctor.IsFppfImage`, its existing fppf-local minimality theorem, and
fppf-local membership in a represented subgroup. It retains arbitrary, including
nonreduced, scheme tests and does not replace fppf images by ordinary pointwise
images.
