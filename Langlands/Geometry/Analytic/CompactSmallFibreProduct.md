# Compact analytic pullbacks along étale morphisms

Worker 659 combines the Library's `CompactFibreProduct` and
`LocalizedEtalePullbackExistence` constructions. The field universe and the
common space and chart-index universe are independent.

`IsCompactSpace.of_iso` transports compactness and Hausdorffness along
the homeomorphism obtained by applying the localized underlying-space
functor to an analytic isomorphism.

For strong maps with compact Hausdorff factors and Hausdorff base,
`isCompactSpace_localization_smallFibreProduct` applies the quotient's
finite chart-pair compactness theorem and its Hausdorff theorem. It then
transfers both instances along the homeomorphism from the quotient to its
shrunk space. This step takes smallness of the quotient as an instance.
`isCompactSpace_recognizedLocalizedPullback` transports the factor and base
instances along the recognition isomorphisms and supplies that smallness
instance using the strong étale hypothesis and finite Banach pushouts.

`compactLocalizedEtalePullback` takes a localized cospan with an étale
first leg, compact Hausdorff factors and a Hausdorff base. It chooses
strong right fractions for the two legs and transports compact
Hausdorffness back along their denominator isomorphisms. The numerator
of the first leg is strongly étale by localized étale composition and
the strong-map criterion. The recognized pullback for the two numerators
has a compact Hausdorff point by the preceding theorem. Transporting its
categorical square along the two denominator isomorphisms gives the
limiting cone over the original cospan, with the same point. The resulting
`CompactLocalizedPullbackData` stores the cone, its full `IsLimit`
witness in the localized category, and compact Hausdorffness.

The construction supplies the compactness and analytic universal property
for the étale-leg case of the geometry used in Task 7491. Its conclusion
concerns a cospan in the localized analytic category.
