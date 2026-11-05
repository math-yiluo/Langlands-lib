# Universe-general smooth manifolds of actual affine points

Let `k : Type u` have `RCLike k`, and let `X` be an affine object over
`Spec k`. The sole additional input to `smoothAffineRegularAtlas hsmooth`
is `hsmooth : SmoothOfRelativeDimension d X.hom`. The definition chooses
an atlas from the published `General.regularChartExistence k X d hsmooth`.
`smoothAffineChartedSpace hsmooth` names its charted space on the actual
relative-morphism carrier `PointTopology.RingPoint k X k`. The charted
space is supplied explicitly as a local instance. No global choice of
charts is installed.

The existing topology on the carrier is retained.
`smoothAffine_topology_eq_evaluation` states, after installing these
charts, that this topology equals the topology induced by the map
`p ↦ (a ↦ regularEvaluation p a)` for all global regular functions
`a : AffineCoordinateRing k X`. Its proof unfolds the published point
and algebra-map induced topologies and applies `induced_compose`.
The evaluations are the actual pullbacks on global sections, as expressed
by the imported `regularEvaluation_eq_pullback`.

`smoothAffineIsManifold` applies `General.RegularAtlas.isManifold` to
this chosen atlas and produces a real `C∞` manifold with model
`Fin d → k`. The real and complex regular-atlas, charted-space and
manifold aliases specialize the same construction to `ℝ` and `ℂ`.
Their real model dimensions are `d` and `2 * d`, as computed by the
imported `real_model_finrank` and `complex_model_finrank`. Constant
relative dimension remains a hypothesis throughout. Zero dimension and
empty point spaces are included.

`smoothAffine_contMDiff_regularEvaluation` gives smoothness of each
global regular function by the corresponding theorem for the chosen
atlas. `smoothAffine_contMDiff_postcomp` applies
`General.RegularAtlas.contMDiff_postcomp` to the chosen source and target
atlases: the actual point map `p ↦ p ≫ f` of any relative morphism is
real `C∞`. The two constant relative dimensions may differ.
`smoothAffinePostcompDiffeomorph` applies the imported actual-isomorphism
construction to `f : X ≅ Y`. Its forward and inverse functions are
exactly postcomposition by `f.hom` and `f.inv`, respectively;
`smoothAffinePostcompDiffeomorph_maps` states these definitional
equalities. Both charted spaces are explicit in the declarations.

`smoothAffineAtlasIndependence` uses
`General.RegularAtlas.independence` to compare this chosen atlas to
any other regular atlas on the same actual carrier, also across model
dimensions. The resulting diffeomorphism has underlying equivalence
`Equiv.refl`. This compares choices by the specified identity
diffeomorphism without equating their atlases.

`smoothAffine_contMDiff_iff_regularSmooth` specializes the published
atlas family criterion directly. Its source has a real normed model
`E : Type v`, chart model `H : Type w` and carrier `M : Type z`, with
`I : ModelWithCorners ℝ E H`, the corresponding topology and
`ChartedSpace H M`. A family into the chosen actual point manifold is
`C∞` exactly when all global regular evaluations along it are `C∞`.
The direct criterion needs no source `IsManifold` assumption. The four
universe parameters `u`, `v`, `w`, `z` are independent.

This is an internal adaptation by Worker 94 of Worker 274's
`PointManifold.SmoothAffineManifold` assembly. It uses the published
universe-general algebraic existence and analytic comparison proofs,
and the `General.RegularAtlasFunctoriality` helpers of Workers 94 and
383. The algebraic and analytic construction proofs remain in their
imported modules. This unit supplies the named construction and its
actual-map interfaces; no original-literature assertion is newly
transcribed here. In particular it does not yet transport this manifold
to completion or base-change carriers or supply adelic differential
growth or reduction theory.
