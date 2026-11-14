# Actual comparison maps for supplied integer-facet models

This internal result works over a Henselian discrete valuation ring `R`
with separably closed residue field and fraction field `K`, in arbitrary
universe and characteristic. It uses the original quotient, full facets
and common-apartment incidence of supplied `IntegerValuationBuildingData`.

The input is a family `D` of actual `RelativeComponentModelData`, one for
each full facet, together with the equality
`(D F).full.integralPoints = characterValuationKernel v G ⊓
B.pointwiseFixer F.val`. The conclusion of
`IntegerFacetModelMorphismsStatement` is that these very models, without
replacement, form `IntegerFacetModelData`. Thus the actual generic-identity
comparison morphisms, including their compatible neutral restrictions,
are constructed rather than supplied.

First, `RelativeComponentModelHom.nonempty_iff_integralPoints_le` proves
that a compatible map between two supplied component-model pairs exists
exactly when the full integral-point images are included. Necessity is the
published full-model point-map naturality. For sufficiency, the proved
`IntegralModel.smoothHomExtension` extends the identity of the original
generic group using the full source model's recorded smoothness. The
published `RelativeComponentModelHom.ofFull` restricts this actual map
through the target relative identity component, with its compatibility
square. `ofIntegralPointsLE` chooses this package.

For incident facets `F ≺ C`, the proved
`IntegerValuationBuildingData.pointwiseFixer_le_of_facetPrecedes` gives
`fixer(C) ≤ fixer(F)`. Intersecting both sides with the same
character-valuation kernel proves inclusion of the full integral-point
images. `morphismOfIntegralPoints` applies the preceding extension
construction. `ofIntegralPoints` assembles these morphisms with exactly
the input family `D`. Its model equality and full integral-point equality
are retained explicitly. The induced inclusion of neutral integral-point
images follows from the constructed neutral map; it requires no separate
formula for those images.

The provenance is a derived composition of the proved smooth Hom
extension, relative-component functoriality and actual integer-building
fixer reversal. The ring and field hypotheses are exactly those needed
by the strictly Henselian extension theorem. No compatibility between
`R` and `v` beyond the explicitly supplied point descriptions is used.
The construction assumes the individual models and their full-point
descriptions. It does not prove their existence, a facet-parabolic
bijection, coefficient descent, special-fibre kernel or torus properties,
or the host prescribed-point split-torus theorem.
