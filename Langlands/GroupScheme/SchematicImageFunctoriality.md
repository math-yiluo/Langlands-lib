# Functoriality of actual schematic-image subgroup functors

This internal derived module works with actual affine group schemes over arbitrary
fields in universe `u`. It compares the all-test subgroup functors represented
by the inclusions of their schematic images. It does not identify these with
the pointwise range of the original map: that range need not be represented by
the schematic image on every test scheme.

`range_inclusion_le_iff` tests containment in any specified closed subgroup
using the original map. The proof descends containment along the schematically
dominant projection to the schematic image, using the published
`SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant`.
`range_inclusion_comp_le` then proves that precomposition shrinks the schematic
image. Applying this in both directions proves invariance under a source
isomorphism (`range_inclusion_iso_comp`).

`range_inclusion_comp_iso` transports the image by an ambient isomorphism.
`range_inclusion_baseChange` proves compatibility with any flat spectrum map
between fields. Both proofs compare closed schematically dominant
factorizations with the published
`SchematicImage.range_eq_of_dominantFactorizations`. The coefficient proof
uses `isSchemeTheoreticallyDominant_baseChange` and preservation of a closed
subgroup under pullback, followed by the published all-test range pullback
formula. Affineness supplies the required quasi-compactness.

These are internal functoriality deductions from `SchematicImage`,
`SchematicImageComparison`, and `SubgroupBaseChange`. No model existence,
parabolicity, smoothness, reductivity, or characteristic hypothesis is asserted.

`SchematicImage.FunctorialityStatement` packages these five conclusions, and
`SchematicImage.functoriality` proves their conjunction. The ground field, all
group schemes, the field extension and the flat spectrum map are arbitrary.
