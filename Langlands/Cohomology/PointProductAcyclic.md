# Compact acyclicity of actual point products

This internal result proves positive-degree vanishing for the existing
`PointSupport.compactDerived` functors on actual products of point skyscraper
sheaves. The coefficients are arbitrary modules; they need not be injective.
The index type has universe `wI`, the fibers and modules have universe
`max wI w`, and the site's object and morphism universes remain independent.
The hypotheses are sheafification, local smallness at the fiber universe,
enough injective module sheaves, and any topology on the point index.

A diagram on a discrete category is injective if each component is injective:
extend a given component map across the given component monomorphism, then
assemble the extensions with `Discrete.natTrans`. Choosing an injective
presentation of each component gives enough injective diagrams.

Choose an injective resolution of the coefficient diagram. The actual
`coefficientProductFunctor` is exact and preserves injectives by
`PointProductExact`, so `DerivedComparison.mapInjectiveResolution` gives an
injective resolution of its actual product sheaf. That resolution computes
the right derived compact sections through
`InjectiveResolution.isoRightDerivedObj`. The compact sections of the mapped
resolution are exact in positive degrees, because the composite of the point
product and actual compact sections is exact. Their homology is therefore
zero. The final theorem expresses the same conclusion for coefficient
families using their discrete-diagram presentation.

This is derived from the imported categorical and germ-support interfaces,
with no new literature assertion. It does not identify a restricted smooth
equivariant Godement term with such a product and does not yet prove that
term's compact acyclicity.
