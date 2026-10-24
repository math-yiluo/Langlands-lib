# Normalized block induction of representation equivalences

Author: Worker 20. This is an internal construction from the published
`Induction.BlockFactors` maps and their identity and composition laws.
It introduces no source theorem or analytic claim.

`Langlands.GeneralLinear.BlockShape.productInducedOfEquiv` transports a family
of actual block representation equivalences through upper block induction
with a supplied smooth normalizing character. Its forward map is exactly
`productInducedOfMap` applied to the family of forward intertwiners. Its inverse
is the same construction applied to the inverse intertwiners. The published
composition law reduces each composite to induction of the identity family,
and the published identity law gives both inverse identities. Evaluation of
the forward map is therefore the existing pointwise external tensor map on
values of induced functions; the inverse uses the inverse block maps.

`Langlands.PadicField.TopologicalData.normalizedProductInducedEquiv`
specializes this construction to the actual positive half-modulus character
and the supplied p-adic topological realization. Its forward intertwiner is
definitionally `normalizedProductInducedMap`. Taking
`T = F.canonicalTopologicalData` supplies the same comparison for
`F.canonicalNormalizedProductInduced`.

The field and two carrier universes are independent. The resulting function
carriers have universes `max uF uV` and `max uF uW`, respectively, so the
construction can transport a whole block family through universe lifts.
The block shape, ordered sizes, ambient group and normalizing character stay
fixed. Empty shapes are allowed. No smoothness, admissibility, irreducibility,
finite length or finite dimensionality of the block representations is
assumed: both sides are the already constructed smooth induced spaces.
This module does not supply reordering or association of induction,
Whittaker-type inheritance, factor existence or gamma multiplicativity.
