# Smoothness from an actual tangent-surjective chart

An identity-preserving morphism of underlying field group schemes, without
a group homomorphism requirement, is surjective on rational identity
tangent vectors if every point of the actual dual-number identity kernel
lifts to the source identity kernel. This follows directly through the
published `Lie.kernelTangentEquiv` with the Library `Picard` tangent maps.

More generally, a map from a smooth scheme over a field to a locally
finite-type field group, surjective on tangent vectors at a rational
source point, makes that group smooth. The existing tangent smoothness
criterion places the source point in the smooth locus of the map. The
image of that smooth locus is a nonempty open set of the target. The
restricted map onto that image is a smooth surjection; smoothness of the
source descends to the image by the published smooth source descent
result. The target group therefore has a nonempty smooth open chart,
and the existing translation and field-extension theorem makes the whole
group smooth over the original field.

The last theorem packages these two results when the smooth source is
itself a group scheme and the chart preserves the identity. There is no
assumption of target smoothness, connectedness, perfectness of the field,
or characteristic restriction. This is an internal composition of the
published tangent and smooth-descent interfaces, with no new external
source translation.

`LieKernelSurjectiveChart` retains the actual smooth source group, chart,
identity equation and identity-kernel lift property as data. Its `smooth`
theorem applies the general criterion to this bundle.
