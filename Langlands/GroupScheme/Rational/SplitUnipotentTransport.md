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
schemes.

Kernel-image membership is the existing `mem_range_kernelι_iff` theorem
from `CentralIsogeny.Basic`.

The torus-action adapters retain both
`TorusActionUnipotenceStatement` and `TorusActionSplitUnipotenceStatement`
as explicit proof premises. For a smooth connected stable closed subgroup
functor `F` in an affine ambient group, the first adapter chooses its smooth
connected closed representative. Its closed inclusion makes that
representative affine. The actual induced action from `RepresentedAction`
is used, and
`actionWeightSpace_onRepresentedSubgroup_eq_bot` from
`Rational.TangentWeightTransport` transfers the absence of zero in the
ambient support to vanishing of the induced action's zero weight space.
The two premises give unipotence and split unipotence of this chosen
representative in that order. The preceding isomorphism transport then
gives both properties for any supplied representative of `F`. The supplied
representative needs no additional smoothness, connectedness, closedness
or affineness assumptions. The ambient group need not be smooth or locally
of finite type for this first adapter; the acting torus is split.

For an ambient group locally of finite type, the next adapter assumes that
the actual tangent submodule of `F` lies in `semigroupWeightSpan b A` and
that zero does not belong to `A`. The published split-torus support bound
in `Rational.SemigroupWeightSupport` excludes zero from the support,
allowing the first adapter to apply. The exact-Lie-image version uses the
published equivalence between `HasLieImage` and tangent-submodule equality.
Finally,
`semigroupSubgroup_unipotent_and_split_of_hasLieImage`
uses the published stability of the actual generated functor to give its
all-representatives clause under explicit smooth connected closed
realization and exact Lie-image hypotheses.

These adapters are internal compositions of the published support,
induced-action and representative-isomorphism results. They prove the
conditional reductions just described. They do not prove either
structural premise, construct the semigroup realization or its exact Lie
image, or establish the unconditional `SemigroupRealizationStatement`.
