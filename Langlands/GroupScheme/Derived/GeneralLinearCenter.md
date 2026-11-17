# Centre of the general linear group on every test scheme

This internal helper proves the centre clause of
`Langlands.GroupScheme.GeneralLinearCenterDerivedStatement` over every
commutative base ring, with any finite index type, including the empty type.
It also identifies the full range of the scalar homomorphism with the centre.
The inherited mathematical provenance is Milne, *Algebraic Groups* (2017),
Example 12.47, as documented in the imported statement pair.

For a central scheme point, its commutation with all points on the same test
scheme transports through `GeneralLinear.pointsEquiv` to membership in the
centre of the invertible matrix group. Mathlib's
`Matrix.GeneralLinearGroup.center_eq_range_scalar` then supplies a unit scalar.
Conversely, a point with scalar matrix factors through `GeneralLinear.scalarTorus`;
the published `GeneralLinear.isCentral_scalarTorus` proves its centrality after
every restriction of test schemes. This proves the assertion for non-affine
and nonreduced tests as well, without a nonempty-index hypothesis.
