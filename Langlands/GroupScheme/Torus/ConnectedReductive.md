# Connected reductivity of a torus from a splitting field

Author: Worker 1567. Moved from the accepted anisotropic finite-quotient
construction during integration.

`Langlands.GroupScheme.IsTorus.isConnectedReductive_of_fieldSplitting`
proves connected reductivity of an actual torus over any field in universe
`u`. It uses the splitting extension contained in `IsTorus`, connected
reductivity of the resulting split torus, and the published field-extension
reflection theorem. It requires no separate affine structure-morphism premise.

This is the same reviewed theorem and proof formerly included in
`Rational/AnisotropicTorusFiniteQuotient`. Its distinct name preserves the
existing `IsTorus.isConnectedReductive` in
`Representation/Plancherel/TorusNormKernelCompactnessReduction`, whose
statement retains an explicit affine structure-morphism instance.
