# Pullbacks of analytic open immersions

This module constructs the inverse image of an open analytic domain and proves
that its inclusion is the categorical pullback of the original inclusion. It
then proves that `SaturatedAtlasPresentation.openImmersion` is stable under
base change, in all three universes of the localized analytic category and over
a complete ultrametric normed field.

`preimageOpenDomain f U hU` is the open domain with underlying set the inverse
image of `U` under the continuous point map of `f`. The restricted morphism
`preimageOpenDomainMap` makes the square with the two domain inclusions commute.
For a cone over this square, commutativity implies that its map to the source
of `f` has image in that inverse image. The published `domainLift` factors the
map through the inverse image domain. Cancellation by the domain inclusions
proves the other projection identity and uniqueness. This proves the full
categorical pullback universal property without assuming a general existence
theorem for analytic fibre products or that underlying spaces preserve them.

`openDomainPullbackIso` identifies any other categorical pullback of this
inclusion with the constructed inverse image domain. Its second projection is
the canonical domain inclusion. Finally, an open immersion is by definition an
isomorphism followed by such an inclusion. Transporting a pullback square along
that isomorphism and using `openDomainPullbackIso` proves
`openImmersion.of_isPullback` and the `IsStableUnderBaseChange` instance.

This is an internal construction and a derived proof from the published
`InvariantAnalyticDomains` universal property and `AnalyticImmersion` definition;
it introduces no additional analytic hypotheses. It is a prerequisite for the
étale target reduction in the algebraic-space analytification comparison, and
does not itself prove that comparison or descent of immersions along étale covers.
