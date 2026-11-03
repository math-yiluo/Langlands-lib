# Opposite dynamic parabolics with the exact standard Levi

This internal construction supplies actual subgroups for an opposite Jacquet
functor. It uses the published standard-cocharacter comparison, dynamic
semidirect decomposition, affine representability, and canonical point-topology
closedness results. It makes no root-opposition or representation-duality claim.

For any group scheme over a base scheme, `Dynamic.inverseCocharacter` precomposes
an actual cocharacter with the power map of exponent minus one on the
multiplicative group. `comp_inverseCocharacter` proves on every test scheme that
its value is the inverse of the original value. Inverting twice returns the
original cocharacter. The centralizer equality is an equality of subgroup
functors on all tests: conjugation by an element fixes a point exactly when the
element commutes with that point, and commuting with an inverse is equivalent to
commuting with the original element. These are consequences of the existing
pointwise group law, not new structural assumptions.

For an actual torus map `i` and cocharacter `ζ`, `oppositeParabolic i ζ` and
`oppositeUnipotent i ζ` evaluate the dynamic parabolic and contraction subgroup
functors for the inverse of `groupHom ζ ≫ i` at the identity test object over
`Spec k`. These definitions do not require any root choice. Under
`StandardCocharacterStatement`, connected reductivity, maximal splitness and
genericity, every `ζ` standard for `rootSet i ν I` has centralizer equal to the
published `standardLevi` at that subset. Centralizer invariance under inversion
then rewrites the published dynamic semidirect decomposition into

`oppositeParabolic i ζ = (levi i ν I) ⋉ (oppositeUnipotent i ζ)`.

Here the equation describes the actual
`IsSemidirectDecomposition` proposition proved by
`opposite_isSemidirectDecomposition`. The Levi is the exact published rational
standard Levi; it is not replaced by an abstract isomorphic group. The only
comparison taken from the standard-cocharacter statement in this proof is its
all-test centralizer equality. The published dynamic decomposition supplies
normalization, inclusions, existence and uniqueness of factorization.

`isClosed_oppositeUnipotent` proves closedness for `pointTopology`, which is the
published evaluation topology transported to identity-test points. An affine
structure morphism makes the ambient group affine over `Spec k`. The published
`Dynamic.Affine.unipotentHom` represents the actual contraction subgroup and is a
closed subgroup. Applying
`PointTopology.isClosed_rationalPoint_subgroup` therefore proves closedness over
a Hausdorff coefficient field. The local-field wrapper derives that Hausdorff
property from `BruhatTits.localField_t2Space`; it adds no closedness premise.

The construction allows every field universe, every actual finite simple-root
subset including the empty one, and general connected reductive groups. Its
local-field wrapper includes positive characteristic. It does not prove
independence of the choice of standard cocharacter, identification with an
opposite root-indexed standard parabolic, an open-cell theorem, Jacquet duality,
or the final Aubert commutation identity. Its intended consumer is a separate
natural Jacquet-duality target using the constructed opposite functor.
