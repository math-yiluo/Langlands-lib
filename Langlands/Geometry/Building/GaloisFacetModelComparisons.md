# Actual coefficient comparisons for supplied integer-facet models

This internal derived unit constructs coefficient comparisons of the original
supplied facet models. Its integral base is a strictly Henselian discrete
valuation ring with the specified fraction field. The field, universe and
characteristics are arbitrary. The individual models and their exact full
integral-point descriptions remain supplied.

`IntegralModel.galoisTwistIsoOfCovariance` treats two different smooth models.
A point of the source twist comes from an original integral section because
the integral coefficient map is an isomorphism. Canonical twist evaluation
is the original coefficient conjugation. Thus covariance of the original
point images supplies the forward inclusion. Inverse conjugation supplies
a section witnessing the backward inclusion. The published theorem
`IntegralModel.smoothHomExtension` extends both generic maps, and generic
rigidity makes them an isomorphism with the specified canonical generic map.
No smooth extension principle is left as an additional premise.

For the original integer-valued building, actual coefficient semilinearity
preserves and reflects pointwise fixation of the entire original full facet.
The published character transport preserves and reflects the valuation
kernel when the coefficient automorphism preserves the valuation. Their
intersection therefore proves covariance of the full-model images from
their exact fixer-point descriptions.

`fullModelGaloisTwistIso` applies the strict extension construction to these
actual images. `neutralModelGaloisTwistIso` restricts that full comparison to
the actual relative identity components by `RelativeComponentCoefficientComparison`.
Generic rigidity proves that the original neutral incidence maps commute
with these comparisons. For a supplied commuting residue coefficient square,
`neutralResidueGaloisIso` specializes the actual neutral comparison, and
`neutralResidueGaloisIso_naturality` proves the original residue incidence square.
`GaloisFacetModelComparisonsStatement` packages full and neutral comparison
existence, and `galoisFacetModelComparisons` proves it from the original
point descriptions and valuation covariance.

The integral and residue coefficient maps and their commuting squares are
specified. Quotient descent comparison, existence of the individual facet
models, the facet-parabolic bijection, integral torus lifting, segment
comparison and the unconditional prescribed-point split-torus theorem are
not established here.
