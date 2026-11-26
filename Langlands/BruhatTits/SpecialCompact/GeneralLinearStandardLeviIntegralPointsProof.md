# The matrix realization of the inherited integral points in a standard Levi

`generalLinearStandardLeviIntegralPoints` proves
`GeneralLinearStandardLeviIntegralPointsStatement`, the block description of
the actual standard Levi of `GL_N` and of its literal intersection with the
standard integral points, used for the inherited subgroup in Renard V.5.1(5).
[Statement](GeneralLinearStandardLeviIntegralPointsStatement.md)

## The Levi on rational points

The diagonal torus is a maximal split torus of the connected reductive group
`GL_N` over the field (`GeneralLinear.isMaximalSplitTorus_diagonalTorus`,
`isConnectedReductive_generalLinear`). Hence `standardCocharacter` applies to
the given generic cocharacter and the Levi index, and its second clause
identifies the standard Levi with the dynamic centralizer of the given
standard cocharacter composed with the torus inclusion.
[Standard cocharacters](../../GroupScheme/Rational/StandardCocharacterStatement.md)

By `GeneralLinear.cocharacterOfWeights_comp_diagonalTorus`, that composite is
the diagonal matrix cocharacter whose integer weights are the coordinates of
the standard cocharacter. The computation
`GeneralLinear.centralizer_diagonalCocharacter` identifies its dynamic
centralizer with the block Levi subgroup functor: the entries between
distinct weight blocks vanish. On rational points,
`GeneralLinear.glRingEquiv_mem_blockLeviSubgroup_iff`, applied to the
equivalence between global sections of the field's spectrum and the field,
turns this into membership of the matrix image in the block diagonal
subgroup over the field. This gives the first equality.
[Matrix dynamics](../../GroupScheme/Dynamic/GeneralLinearOrbit.md)

## The intersection with the integral points

By `GeneralLinear.mem_standardIntegralModel_integralPoints_iff`, a rational
point is integral exactly when its matrix is the image of an invertible
matrix over the valuation ring. If the point also lies in the Levi, the
entries of that lift between distinct blocks have zero image in the field,
so they vanish because the valuation ring injects into its fraction field.
Conversely, an invertible block diagonal matrix over the valuation ring
maps to a block diagonal matrix over the field
(`GeneralLinear.map_mem_blockLeviSubgroup`); the corresponding rational
point is integral, and it lies in the Levi by the first part. Both
directions use the same ambient rational-point matrix equivalence.
[Integral points](../../GroupScheme/IntegralModel/GeneralLinearStandardPoints.md)
