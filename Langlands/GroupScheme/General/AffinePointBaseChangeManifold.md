# The actual affine point manifold through algebraic base change

Author: Worker 94.

Let `C` be a commutative ring, let `k` be an `RCLike` field in the same
arbitrary universe, and fix `Algebra C k`. Let `G` be an actual group scheme
over `Spec C` with affine underlying scheme. Write `G_k` for the existing
pullback group scheme. The source points remain
`G.affinePoints (CommAlgCat.of C k)` with their original categorical group
law and regular-function evaluation topology. The target is
`PointTopology.RingPoint k G_k.X k` with its existing evaluation topology.
The local topology instances are explicit aliases of the published group
point topologies.

`affineBaseChangePointHomeomorph` composes the actual multiplicative
scalar-extension homeomorphism
`affinePointsBaseChangeContinuousMulEquiv C k k G` with
`G_k.affinePointsRingPointHomeomorph`. The latter has the identity as its
underlying point map. Thus the composite is precisely the actual
pullback-adjunction map, followed by the existing identification of the two
relative-morphism point carriers. No point carrier, group law or topology
is replaced.

Fix `hsmooth : SmoothOfRelativeDimension d G.X.hom`.
`affineBaseChange_smooth` proves the same constant-relative-dimension
property for `G_k.X.hom`. Its body identifies that structure morphism with
the actual pullback's second projection and applies Mathlib's
`MorphismProperty.pullback_snd` to the published stability of
`SmoothOfRelativeDimension d` under base change. This theorem needs no
affineness assumption. Target algebraic smoothness is consequently a
proved consequence, rather than a separate analytic premise.

`affineBaseChangeChartedSpace` installs exactly
`PointManifold.General.smoothAffineChartedSpace
(affineBaseChange_smooth C k G hsmooth)` at the target and pulls these
specified charts back through `affineBaseChangePointHomeomorph` using
`Geometry.Manifold.pullbackChartedSpace`. The preferred source chart is
therefore the actual homeomorphism followed by the preferred target chart.
The existing source topology is retained. `affineBaseChangeIsManifold`
uses the target's proved manifold theorem and the exact transition
cancellation of the pullback construction. The real model is
`Fin d → k`, with order `∞`; zero dimension is allowed.

`affineBaseChangeDiffeomorph` bundles precisely this scalar-extension
homeomorphism and its inverse as a diffeomorphism between the pulled
source atlas and the exact named target atlas.
`affineBaseChangeDiffeomorph_toEquiv` states by reflexivity that its
underlying equivalence is that of `affineBaseChangePointHomeomorph`.
No compatibility with an independently specified source atlas is assumed
or asserted.

For any real charted parameter space `M` and model with corners `I`,
`affineBaseChange_contMDiff_iff_coordinateSmooth` identifies ordinary
smoothness of `p : M → G(k)` in this constructed manifold with the original
`G.CoordinateSmooth (CommAlgCat.of C k) (RingHom.id k) I p`. Thus all original
global-function values are tested before scalar extension. The proof
composes three proved equivalences: the explicit pullback family criterion,
the named target manifold's coordinate criterion, and
`coordinateSmooth_baseChange_iff C k k G`. The source needs only a charted
structure, with no source manifold assumption. The normed model and chart
model share one universe as required by `CoordinateSmooth`; the coefficient
and parameter-carrier universes are independent.

`affineBaseChangeLieGroup` proves a real `C∞` Lie group for the literal
original categorical point law and these exact charts. It installs the
constructed manifold. For multiplication it applies the family criterion,
uses the smooth first and second projections, and applies the published
original-coordinate multiplication theorem. For inversion it applies the
same criterion to the identity family and the published coordinate inverse
theorem. No smoothness of either group operation is assumed.
`affineBaseChange_contMDiff_evaluation` applies the family criterion to the
identity family, proving smoothness of every original regular-function
value.

This is an internal assembly of the published actual scalar-extension
comparison and coordinate-smoothness proofs, the General named affine
manifold and group-family comparison, and the explicit homeomorphism chart
transport. No new original-literature transcription is made. All
constant-relative-dimension algebraic smoothness hypotheses remain
explicit; this file does not derive them from connected reductivity. It
also supplies no differential-growth, quotient-measure or reduction
statement. Actual completion specialization and the finite archimedean
product remain subsequent constructions.
