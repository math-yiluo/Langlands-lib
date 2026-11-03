# Orbit contractions through normalized open products

This internal geometric construction specializes `Dynamic.orbitOpenLift` to the
multiplication presentation of two group homomorphisms over an arbitrary field.
`identity_mem_product_opensRange` puts the identity point in that presentation
by using the pair of identity morphisms.

If the presentation is an open immersion and both ranges are normalized by a
cocharacter, `openProductOrbitLift` constructs an actual lift of any orbit
extension whose value at zero is the identity. The product stability theorem
supplies stability, and identity membership supplies its zero condition.
`openProductOrbitLift_fac` proves that composition with multiplication recovers
the original extension.

For represented subgroup functors, `hasProductContraction_of_openProduct`
feeds that lift to the existing represented-lift adapter. It proves the actual
`HasProductContraction` predicate on the whole affine line. The field, universe,
and separated group-scheme scope are those of the orbit lift; the open immersion
and normalization remain explicit hypotheses. The argument is an internal
deduction from the imported constructions and does not establish an opposite-cell
theorem or rational Bruhat decomposition.
