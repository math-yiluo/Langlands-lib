# Differentiating an equivariant map of genuine smooth carriers

`SmoothUnitsIntertwinerLieStatement` concerns jointly continuous representations of the units group of a complete finite-dimensional real normed algebra. A continuous complex-linear map between their genuine smooth carriers that commutes with the group action commutes with the derived action in every real algebra direction.

For a direction \(X\), the line \(1+tX\) represents a curve through the identity in the units chart. `hasDerivAt_unitsChartOrbit` differentiates its orbit in the genuine smooth topology. The equivariance identity makes the target curve equal to the image of the source curve under the given continuous linear map. Restrict scalars to the reals, pass that map through the slope, and use uniqueness of the limit to identify the two derived vectors.

This proves the differentiation step for restricting continuous equivariant maps of real standard smooth models to intertwiners of their compact-finite vectors.
