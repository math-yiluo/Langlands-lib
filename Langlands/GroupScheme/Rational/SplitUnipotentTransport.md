# Transport of actual unipotence and split series

This internal helper unit develops isomorphism transport for the published
actual group-scheme definitions. It uses no external structural theorem.
Its purpose in the semigroup realization proof is the clause asserting
unipotence and split unipotence for every representative: once one
representative has those properties, uniqueness of representation identifies
all the others with it.

`vectorCoordinatesOfIso` transports each multiplicative coordinate equivalence
by precomposing with the inverse group-scheme isomorphism on the same test
scheme. The accompanying naturality proof gives
`IsVectorGroupOfDimension.of_iso`.

`SubgroupFunctor.range_comp_iso` describes the range of an inclusion followed
by an isomorphism as the inverse image under the inverse isomorphism.
`mem_range_kernelι_iff` uses the existing scheme-kernel point
equivalence to identify its range on every test with the points killed by
the homomorphism. These give `IsFppfQuotient.comapIso`: flatness,
surjectivity, and local finite presentation are preserved by composing with
an isomorphism, and the kernel equality is checked on all test schemes.

`HasSplitSeries.of_iso` preserves the length of the finite normal Ga-series.
For length zero, the inverse isomorphism transports the assertion that all
points are the identity. For a positive length it transports the first
inclusion and quotient map, retains the existing kernel series and
one-dimensional vector quotient, and transports normality by inverse image.
`IsSplitUnipotent.of_iso` then retains that finite length.

`IsUnipotent.of_iso` restricts any coefficient representation along the
inverse isomorphism. Its nonzero fixed vector for the other group remains
fixed on every test scheme, since each original point is the image of its
inverse-isomorphism preimage.
`unipotent_and_split_of_representatives` applies these two transport results
to the existing canonical isomorphism between two representatives of the
same subgroup functor.

All constructions are universe-polymorphic and retain arbitrary test
schemes. They do not construct a split series or prove unipotence of a new
group.

Kernel-image membership is the existing `mem_range_kernelι_iff` theorem
from `CentralIsogeny.Basic`.
