# Generic images of special-fibre subgroup preimages

This internal construction uses the published `IntegralModel.reduction` and
`IntegralModel.integralPointMap`. For a local domain `R`, its fraction field
`K`, an integral model `M`, and any subgroup `P` of the actual residue-field
points of `M.specialFibre`, `specialFibreSubgroupPoints P` is the generic
image of the inverse image of `P` under reduction.

The membership theorem unfolds the subgroup image: a point belongs precisely
when an integral section reduces into `P` and evaluates to that generic point.
Every such point belongs to `M.integralPoints`, as witnessed by the same
section. The construction retains arbitrary universe `u` and assumes no
smoothness, reduction surjectivity, or radical property.

This is derived content, not a new assertion from the literature. It
generalizes the subgroup-image expression used in
`SpecialFibreQuotientData.positivePoints` and can be applied to the point
image of any represented special-fibre subgroup. The construction does not
identify any subgroup with an actual unipotent radical or a quotient kernel.
