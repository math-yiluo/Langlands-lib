# Explicit pullback of a specified manifold structure

This internal construction by Worker 94 uses Mathlib's chart, structure
groupoid and manifold definitions. Given a homeomorphism `e : M ≃ₜ N`
and a specified charted space on `N`, `pullbackChartedSpace e` retains the
given topology on `M`. Its atlas is the image of the target atlas under
`c ↦ e.transOpenPartialHomeomorph c`; its preferred chart at `x` is
`e.transOpenPartialHomeomorph (chartAt H (e x))`.

`pullbackChart_transition` proves equality of each transition with the
corresponding target transition. It checks the forward map, inverse map
and source, cancelling the actual homeomorphism with its inverse.
`pullbackIsManifold` uses this equality and target chart compatibility to
give the pulled structure the same manifold model and differentiability
order. No topology or chart choice on the target is replaced.

`contMDiff_pullback_toFun` and `contMDiff_pullback_invFun` express each
actual map in the specified preferred charts. Cancellation reduces its
differentiability to that of the identity in the target charts.
`pullbackDiffeomorph` bundles precisely these maps and the underlying
equivalence of `e`. These two smoothness results require only a charted
target; the manifold result additionally requires the target manifold.
All models with corners and all differentiability orders are allowed.

`contMDiff_pullback_iff` characterizes parameter families into the pulled
space by smoothness after composition with `e`.
`contMDiff_from_pullback_iff` characterizes maps out by composition with
`e.symm`. Each direction composes with one of the proved smooth maps;
cancelling the homeomorphism proves the converse. The parameter or target
space needs only a charted structure, with its own model and independent
universes.

This supplies transport to a deliberately pulled atlas. It makes no
claim of smoothness between two independently pre-existing atlases.
There is no new transcription from external literature.
