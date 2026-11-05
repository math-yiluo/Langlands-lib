# Dimension of quotients by smooth connected kernel cores

Worker 1569, extending the Library construction to perfect fields.

The construction retains the actual kernel, its reduced identity core, the
represented smooth quotient by that core, and the descended group homomorphism
from `KernelCoreQuotient`.

The reduced identity core has open underlying range: its range is the image of
the open identity component under the homeomorphism from a scheme's reduction.
The induced map of full kernels is smooth and open. It sends the core to the
identity, so the identity is isolated in the full kernel of the descended map.
The descended map is consequently quasi-finite at its rational identity point.
Comparing stalk dimensions at closed rational identity points bounds the smooth
connected quotient's relative dimension by that of a smooth target of constant
relative dimension.

For a nonzero map to a one-dimensional smooth target, the quotient dimension is
at most one. If it were zero, the quotient would be étale and its rational unit
section would make it trivial by
`eq_zero_of_smoothOfRelativeDimension_zero_over_field`. The descended map would
then be zero, contradicting the original nonzero map. The quotient therefore
has relative dimension one.

This is a derived prerequisite for the perfect-field unipotent splitness proof.
It generalizes the existing algebraically closed argument, retaining its actual
scheme maps and all-test kernel statements. Perfectness is used for the smooth
reduced kernel core; dimension-zero triviality itself works over every field.
