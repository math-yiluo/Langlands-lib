# Vector coordinates under field extension

This internal construction starts with supplied vector-coordinate group
isomorphisms on every relative test scheme for a group scheme `V` over an
arbitrary field `k`. Both fields and the schemes lie in universe `u`; the vector
dimension may be zero.

For any field extension `K/k`, `vectorBaseChangeCoordinates` gives coordinates
on the actual base change of `V`. On a test scheme over `Spec K`, it first
uses the actual pullback-point group isomorphism and then the original
coordinates on the same test scheme viewed over `Spec k`. The underlying
scheme, and hence its ring of global functions, remains the same.

`IsNaturalVectorCoordinates.baseChange` proves naturality of these coordinates
under every morphism of tests over `Spec K`, using the original naturality and
that of the pullback-point comparison.

For an actual action of an arbitrary group scheme `H` on `V`,
`IsLinearVectorCoordinates.baseChange` proves scalar-linearity of the pulled-back
action in these transported coordinates. The proof uses the exact action
intertwining formula from `AutomorphicAction.BaseChange`; all scalars still
belong to the same test scheme's ring of global functions.
`IsLinearVectorCoordinates.restrict` retains the original coordinates when
the acting group is restricted along an actual group-scheme homomorphism.

`vectorAffineCoordinates_baseChange` identifies the transported coordinates
on each affine coefficient algebra `A` with the original affine coordinates
through `Lie.affineBaseChangeEquiv`. The supplied `k`- and `K`-algebra structures
on `A` must form a scalar tower. The proof applies coordinate naturality to
`Lie.affineBaseTestIso`, whose underlying scheme map is the identity.

The provenance is the existing actual pullback-point, natural coordinate,
scalar-linearity and affine-test interfaces. The module derives transport
formulas directly from those definitions. It imposes no splitness assumption
and proves no cocycle vanishing or rational conjugacy theorem.
