# Relative parabolic subgroups are closed

Worker 589, with the local comparison development by Worker 636.

`Langlands.GroupScheme.relativeParabolicClosed.{u}` proves exactly the published
`Langlands.GroupScheme.RelativeParabolicClosedStatement.{u}`. For every scheme
`S`, reductive group scheme `G/S`, group scheme `P/S`, and homomorphism
`i : P → G` satisfying `IsRelativeParabolicSubgroup i`, its underlying morphism
is a closed immersion. The universe is arbitrary. There are no additional
hypotheses on the base or the inclusion. The target statement and its imports
are unchanged.

## Implemented proof

The proof first establishes `relativeParabolicEtaleLocalDynamic`, the
previously stated etale-local dynamic description of the actual inclusion.
Geometric connectedness of `G/S` follows from reductivity. The supporting
`ParabolicPointedLifting` module proves geometric connectedness of `P/S` from
its parabolic residue fibres, without assuming relative closedness.

At each point `s` of `S`, `relativeParabolicPointedDynamicLifting` supplies an
etale map `p : U → S`, a specified map `b : Spec κ(s) → U` over `s`, and a
cocharacter `χ : G_m,U → P_U`. On the actual iterated pullback along `b`, the
inclusion is closed and represents the dynamic parabolic of `χ` composed with
the inclusion. That lifting theorem factors a field defining cocharacter
through the field parabolic and uses smooth representability of the
split-source Hom functor with the pointed smooth-section construction.
Canonical pullback and multiplicative-group comparisons retain the precise
fibre identity.

`LocalDynamicComparison.exists_open`, applied over `U`, extends this dynamic
identity to an open map `q : V → U` through which `b` factors. Its hypotheses
are satisfied by the smooth affine families with geometrically connected
fibres and the monicity of the base-changed inclusion. The comparison itself
uses representatives of the dynamic parabolics in `P_U` and `G_U`, compares
them at the specified field point, and applies the open isomorphism criterion
for monic maps of such families. Only the specified field inclusion is
assumed closed at that step.

The helper `isRepresentedBy_dynamicParabolic_direct` transports the resulting
representation from the iterated pullback along `p,q` to the direct pullback
along `q ≫ p`. Naturality of `Descent.pullbackComparison` gives the inclusion
square; invariance of the dynamic functor under the ambient isomorphism and
invariance of the range under the source isomorphism give the subgroup
identity. Monicity is transported by cancelling the source isomorphism.

The composite `q ≫ p` is etale. The specified field point of `V` maps to `s`.
`exists_etaleCover_of_pointedDynamic` chooses one such neighbourhood per point
and uses these field points to prove joint surjectivity, producing the desired
etale cover and its dynamic representations. This also covers an empty base.

Finally, `relativeParabolicClosed_of_etaleLocalDynamic` applies arbitrary-base
dynamic representability to obtain a closed representative on each cover
member. Uniqueness of representatives makes the actual local inclusion
closed. Finiteness descends over the pulled-back fppf cover of the ambient
scheme, and the original monicity makes this finite morphism a closed
immersion.

## Provenance

This proof is an internal composition of the supporting pointed lifting,
local dynamic comparison, cover transport and closedness descent results.
The target's source is Conrad, *Reductive group schemes* (2014),
Proposition 5.2.3, first assertion; its original-source correspondence is
recorded in the unchanged target pair. The implemented route uses pointed
cocharacter lifting rather than choosing a relative maximal torus. It does
not use relative parabolic closedness as an input or assume an affine or
Noetherian base.
