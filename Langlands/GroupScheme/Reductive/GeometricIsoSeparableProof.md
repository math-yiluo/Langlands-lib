# Geometrically isomorphic reductive groups over a finite separable extension

`Langlands.GroupScheme.reductiveGeometricIsoSeparable.{u}` proves
`ReductiveGeometricIsoSeparableStatement.{u}`. Let `G` and `H` be connected
reductive groups over `k` whose base changes to `AlgebraicClosure k` are
isomorphic. Their base changes to a finite separable extension `L/k` are
isomorphic as group schemes.

`maximalTorusExistence` gives a maximal torus in each group.
`IsTorus.commonFiniteGaloisSplitting` supplies a single finite Galois field
`L` over which both tori split. `maximalTorusBaseChange` keeps both tori
maximal, and `IsMaximalTorus.isFibrewiseMaximalTorus` gives the corresponding
maximality on residue fibres of `Spec L`. Connected reductivity ascends by
`IsConnectedReductive.baseChange_of_algebraicExtension`, and
`IsConnectedReductive.isReductive` gives reductivity over `Spec L`.

The embedding `L →ₐ[k] AlgebraicClosure k` makes the original algebraic
closure an algebraically closed `L`-algebra. `baseChangeFieldTowerIso`
identifies direct base change from `k` to this field with base change through
`L`. This transports the given geometric isomorphism to the geometric
fibres of the two groups over `L`. `localSplitReductiveGeometricIso` then
produces the desired isomorphism over `L`. The separability of `L/k` follows
from its Galois property.

This implements J. S. Milne, *Algebraic Groups* (2017), Corollary 23.28 and
its use of Corollary 23.27, printed p. 493 (PDF p. 509). The source ID is
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
