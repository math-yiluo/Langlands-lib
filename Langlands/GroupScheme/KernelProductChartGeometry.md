# Smoothness and connectedness of kernels in product charts

This internal supporting module composes the actual finite-product and
kernel-chart APIs. It introduces no new assertion from the literature and
assumes no unproved geometric statement. Full-scheme chart containment and
all factor geometry are retained explicitly.

`smooth_geometricallyConnected_pi` proves that a finite product of smooth
group schemes with geometrically connected fibres again has both properties,
over any base scheme and including the empty product. The conjunction of
smoothness and geometric connectedness is stable under base change and
composition: smoothness supplies the openness needed by geometric
connectedness. Identities have the properties. The published
`prop_pi_hom` then applies to the actual limiting product fan.

`smooth_connected_pi_of_affine` works over any field. Each factor is supplied
as smooth, affine and connected. Smoothness gives local finite type and
affineness gives quasi-compactness, so the published theorem
`geometricallyConnected_of_connected` for finite-type group schemes promotes
ordinary connectedness to geometric connectedness. Applying the preceding
finite-product result and the connectedness theorem over a one-point field
spectrum proves smoothness and connectedness of the product.

`KernelProductChart.smooth_connected` has all the chart hypotheses of
`KernelProductChart.iso`: compatible monomorphic scheme charts, target chart
preserving the distinguished unit, and a morphism from the actual full
scheme kernel into the source product chart whose composite is the kernel
inclusion. It also assumes that every actual factor kernel is smooth, affine
and connected. The preceding result gives a smooth connected product.
The comparison isomorphism over the unchanged field base transfers smoothness
by the structural-map equation and connectedness by the underlying
homeomorphism.

The charts need not preserve multiplication. Thus this construction uses
only the scheme isomorphism and makes no group-product or unipotence claim.
Obtaining compatible charts, full-scheme containment and factor kernel
geometry remains the consumer's obligation.
