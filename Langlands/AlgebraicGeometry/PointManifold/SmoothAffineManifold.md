# The real smooth manifold of actual smooth affine points

For an affine object `X : Over (Spec (CommRingCat.of k))`, with `k : Type`
an `RCLike` field, `smoothAffineRegularAtlas hsmooth` chooses an atlas from the
proved `regularChartExistence k X d hsmooth`. Its sole additional input is
the algebraic hypothesis `hsmooth : SmoothOfRelativeDimension d X.hom`.
No analytic chart, rank, comparison or manifold hypothesis is supplied by
the caller. `smoothAffineChartedSpace hsmooth` is the resulting named
charted space on the actual relative-morphism carrier `RingPoint k X k`.
It is used as an explicit local instance; this module installs no global
choice of charts.

The charts are the published `RegularAtlas.chartedSpace` on the already
installed affine evaluation topology. In particular the construction
introduces no new topology. `smoothAffine_topology_eq_evaluation` states
this explicitly after installing the chosen charts: the topology equals
the topology induced by the map sending an actual point to the function
of all its global regular-function values. Its proof unfolds the two
published induced topologies, on actual scheme points and on algebra-map
points, and applies `induced_compose`. The evaluations are the actual
pullbacks on global sections, by `regularEvaluation_eq_pullback`.

`smoothAffineIsManifold` applies the published `RegularAtlas.isManifold`
to the chosen atlas. This gives a real `C∞` manifold with model
`Fin d → k`. The real and complex aliases
`realSmoothAffineRegularAtlas`, `complexSmoothAffineRegularAtlas`,
`realSmoothAffineChartedSpace`, `complexSmoothAffineChartedSpace`,
`realSmoothAffineIsManifold` and `complexSmoothAffineIsManifold` provide
both actual coefficient specializations. The published
`real_model_finrank` and `complex_model_finrank` compute their real model
dimensions as `d` and `2 * d`. Every construction retains the constant
relative dimension hypothesis. There is no positive dimension or
point nonemptiness assumption, so the results include `d = 0` and empty
actual point spaces.

`smoothAffine_contMDiff_regularEvaluation` applies the published
`RegularAtlas.contMDiff_regularEvaluation` to this same atlas.
`smoothAffine_contMDiff_postcomp` applies
`RegularAtlas.contMDiff_postcomp` to the chosen source and target atlases.
It proves that the actual map `p ↦ p ≫ f`, for any relative morphism
`f : X ⟶ Y`, is real `C∞`; the source and target may have different
constant relative dimensions. The charted-space arguments are explicit
in the theorem type.

`smoothAffinePostcompDiffeomorph` similarly specializes
`RegularAtlas.postcompDiffeomorph` to an actual isomorphism `f : X ≅ Y`.
`smoothAffinePostcompDiffeomorph_maps` records that its two maps are
exactly `p ↦ p ≫ f.hom` and `q ↦ q ≫ f.inv`; both equalities are
definitional. This includes changing the affine presentation by an actual
isomorphism. `smoothAffineAtlasIndependence` applies the first conjunct
of the published `regularAtlasCanonicality`: from the chosen construction
to any other valid regular atlas on the same actual point carrier there
is a `C∞` diffeomorphism whose underlying equivalence is exactly the
identity. Both charted-space arguments are explicit, so this statement
also applies when they share a carrier but differ in charts or model
dimension. Together these results express canonicality up to the specified
actual maps, rather than equality of the chosen atlases.

`smoothAffine_contMDiff_iff_regularSmooth` applies the second conjunct of
`regularAtlasComparison.{v,w,z}` to the chosen atlas. Its source has a
real normed model `E : Type v`, a topological chart model `H : Type w`
with `I : ModelWithCorners ℝ E H`, and a carrier `M : Type z` with
explicit `TopologicalSpace`, `ChartedSpace H M` and `IsManifold I ∞ M`
hypotheses. A family `f : M → RingPoint k X k` is `C∞` for the constructed
target exactly when `RegularSmooth I f` holds, that is, when every global
regular-function evaluation along `f`, valued in `k` as a real normed
space, is `C∞`. The construction was obtained from the algebraic theorem
before applying this criterion.

This is an internal assembly of the published algebraic chart-existence,
analytic comparison and canonicality proofs, imported by Lean name.
The substantial standard-smooth and inverse-function construction remains
in `RegularChartExistenceProof` and its dependencies; the substantial
family comparison and canonicality proofs remain in
`RegularAtlasComparisonProof` and `RegularAtlasCanonicalityProof`.
This module makes no new transcription or literature claim. The separate
group specialization uses the existing actual point group law and the
published regular-atlas group adapters.
