# The actual infinite adelic group manifold

Author: Worker 94. This internal construction assembles the specified local
completion manifolds using the finite-product atlas and explicit homeomorphism
chart transport. It imports the published actual completion decomposition and
mixed-coordinate comparison by their Lean names.

Let `F` be a number field in any universe, and let `G` be an affine group scheme
over `F`. Assume `SmoothOfRelativeDimension d G.X.hom` for a natural number `d`.
Constant relative dimension remains an explicit algebraic hypothesis. The
construction works on the original `InfiniteAdelicGroupPoints F G`, whose points
are relative scheme morphisms over the actual infinite adele ring and whose
topology is the original regular-function evaluation topology.

`smoothModel F d` is the finite dependent product
`(v : InfinitePlace F) → Fin d → v.Completion`, viewed as a real normed vector
space. The statements explicitly pin the compatible `completionRCLike F v`
structures. These retain the actual normed fields and completion topologies, as
explained in `InfinitePlaceGroupManifold`.

`productChartedSpace` takes precisely the finite-product charts of the named
local `InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth`.
`productIsManifold` applies the finite-product compatibility theorem to the
proved local manifold instances. The product uses its ordinary product topology.
`smoothChartedSpace` pulls this exact atlas back through
`(completions F G).toHomeomorph`, the actual decomposition of infinite adelic
group points into their points over the completions. `smoothIsManifold` proves
compatibility of these pulled charts on the original topology.

`completionsDiffeomorph` is this same completion decomposition, now as a
diffeomorphism between the specified atlases. Its `toEquiv` is definitionally
the `toEquiv` of `completions F G`, as recorded in
`completionsDiffeomorph_toEquiv`. Its inverse is the original assembly map.
No equality of independently chosen atlases is asserted.

For a family from any real charted space with a model with corners `I`,
`contMDiff_iff_places` characterizes manifold smoothness into the original
infinite adelic group by smoothness of every actual completion projection.
The parameter space need not satisfy an `IsManifold` hypothesis; its model and
carrier universes are independent of that of `F`.

`contMDiff_iff_coordinateSmooth` identifies this manifold smoothness with the
original `G.CoordinateSmooth` criterion: for every original global regular
function on `G`, its value is smooth after the specified
`InfiniteAdeleRing.ringEquiv_mixedSpace F`. The target is the existing mixed
real/complex space, with real differentiability. The proof combines the product
family criterion, the local real and complex coordinate criteria and
`coordinateSmooth_iff_completions`. Every infinite place is real or complex,
which supplies the converse from the two subtype-indexed collections of tests.

`smoothLieGroup` proves that the existing multiplication and inversion on the
original group are smooth for these charts. The proof uses the mixed-coordinate
criterion, the two smooth product projections and the identity family, together
with the proved `CoordinateSmooth.mul` and `CoordinateSmooth.inv` results for
the original affine group operations. Its manifold field is `smoothIsManifold`.
No analytic group-law smoothness is supplied as a premise.

`contMDiff_atPlace` proves smoothness of the original completion projections.
`contMDiff_assemble` is smoothness of the inverse completion diffeomorphism.
`contMDiff_mixedEvaluation` proves smoothness of each original regular-function
value in the specified mixed coordinates. `contMDiff_completionEvaluation`
proves smoothness of the value at each actual completion; it uses the local
coordinate criterion and the existing exact `atPlace_evaluation` identity.

The provenance is internal assembly of the actual affine-point completion
manifolds, explicit homeomorphism chart transport, the finite-product helper and
published original-coordinate identities. This unit constructs the infinite
adelic manifold and original Lie group under the stated constant-dimension
hypothesis. Deriving that hypothesis from connected reductivity, compatibility
with existing general-linear manifold charts, differential growth, reduction
theory, quotient measures and automorphic Hilbert spaces remain separate
obligations.
