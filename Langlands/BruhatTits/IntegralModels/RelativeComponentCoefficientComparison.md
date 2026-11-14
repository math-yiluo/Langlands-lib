# Actual coefficient comparisons for supplied neutral models

This internal derived unit constructs coefficient comparisons of the actual
neutral integral models from supplied comparisons of the actual full models.
The integral base is an arbitrary domain with specified fraction field. No
characteristic assumption is made, and the universe is arbitrary.

`mapNeutral` restricts a compatible full-model homomorphism with any specified
generic-group map to the supplied relative identity components. The source
neutral model has geometrically connected fibres by
`RelativeComponentFunctoriality`, so its composite with the target full
model factors through the target neutral model by `toNeutral`. The original
generic map is retained. Applying this in both directions and using generic
rigidity gives `neutralIsoOver` and its inclusion square.

`RelativeComponentModelData.twist` pulls back both original integral models
and their inclusion along the specified integral coefficient map. Their
generic identifications use the canonical commuting-square comparison and
the specified generic coefficient map. Smoothness and geometric
connectedness survive base change, as does the relative-component property.
`neutralTwistIso` consequently constructs the actual neutral coefficient
isomorphism from an actual full one and preserves its inclusion square.
`CoefficientComparisonStatement` packages this construction, and
`coefficientComparison` proves it.

`IntegralModel.twist_comparison_naturality` proves the integral incidence
square without assuming it. Both paths extend the same specified generic
isomorphism, since the original incidence maps extend identity maps.
Published generic rigidity identifies the actual integral maps.

For a local integral base, `IntegralModel.Iso.residueTwistIso` constructs an
actual special-fibre coefficient isomorphism from an actual integral one.
It composes the canonical comparison for the residue coefficient square
with the residue pullback of the integral isomorphism. The theorem
`residue_twist_comparison_naturality` proves the original special-fibre
incidence square from integral rigidity and naturality of the canonical
square comparison.

All inputs are actual group schemes, models and morphisms. Existence of the
full-model coefficient isomorphisms remains supplied. No quotient descent
comparison, facet-parabolic bijection, integral torus lift or unconditional
building-point split-torus theorem is asserted.
