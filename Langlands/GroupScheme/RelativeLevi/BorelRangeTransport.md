# Relative Borel subgroups and represented subgroup functors

This module is a derived consequence of the existing relative Borel predicate
and uniqueness of representations of a subgroup functor. It adds no Borel
existence assertion and uses no reductivity hypothesis on the ambient group.

`IsRelativeBorelSubgroup.of_range_eq` starts with a relative Borel inclusion and
a second monic inclusion with equal subgroup functors on every test scheme.
The two inclusions represent the same subgroup functor, so
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` gives an isomorphism
between their source group schemes that commutes with their inclusions.
Its inverse identifies the second inclusion with the original inclusion
precomposed by a source isomorphism.

The proof pulls this isomorphism to each residue field and uses the published
geometric Borel source-isomorphism transport theorem. These geometric Borel
fibres also supply the required parabolic fibres. Smoothness and affineness of
the second source follow from the source isomorphism, and its monicity is the
explicit premise.

`isRelativeBorelSubgroup_iff_of_range_eq` applies this argument in both
directions when both presentations are monic. Equality here is equality of
subgroup functors on all test schemes, rather than equality of geometric point
sets.

`relativeBorelOfRangeEq` performs this transfer on actual subgroup data. It
returns the specified second inclusion, with its specified source and ambient
group, together with its proved relative Borel property. Its underlying
inclusion is definitionally the input inclusion, as recorded by
`relativeBorelOfRangeEq_val`.
