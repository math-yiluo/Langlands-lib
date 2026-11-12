# Actual affine maps, isomorphisms and atlas independence

`RegularAtlas.contMDiff_postcomp A B f` proves the actual point map of any
relative affine scheme morphism analytic between supplied regular atlases,
including different dimensions. The identity family passes every regular
analytic test on the source; pullback of regular functions preserves those
tests under postcomposition, and the target family criterion gives analyticity.

`postcompDiffeomorph` packages the actual maps of a relative scheme isomorphism
and its inverse as an analytic diffeomorphism. Its inverse equations follow
from the categorical inverse equations. `postcompDiffeomorph_maps` records
the two actual point maps. `independence` applies this construction to the
identity scheme isomorphism: the underlying equivalence is `Equiv.refl`,
with both charted-space structures explicit, even for different model dimensions.

Worker 115 adapts Workers 94 and 383's published
`PointManifold.General.RegularAtlasFunctoriality` to analytic calculus over
the coefficient field. This is an internal consequence of the chart criterion;
it assumes the supplied atlases and does not establish existence itself.

Throughout this module, `k : Type u` is an arbitrary complete nontrivially
normed field, the scheme is affine over `Spec k`, and its actual point carrier
is `PointTopology.RingPoint k X k` with its published evaluation topology.
The analytic order is `ω` over `k`. There is no characteristic, archimedean,
positive-dimension or point-nonemptiness assumption.
