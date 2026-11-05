# The original group on the universe-general affine manifold

Let `k : Type u` be an `RCLike` field and `G` an actual group scheme
over `Spec k` with affine underlying scheme. All point groups here use
the original categorical law `G.ringPointGroup (CommAlgCat.of k k)` on
`PointTopology.RingPoint k G.X k`. Their topology is the existing
regular-function evaluation topology. The module installs its group,
topology and charted-space instances locally.

`regularSmooth_iff_coordinateSmooth` compares the universe-general
`PointManifold.General.RegularSmooth` test with the published
`G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k)`. The family on
the first side is transported by the original
`G.affinePointsRingPointHomeomorph`. Its evaluation identity proves
that both predicates test the same global-function values. This needs
only a charted source. `regularSmooth_inv` and `regularSmooth_mul`
then transfer the published coordinate-smooth preservation theorems
through that same homeomorphism. The multiplication and inversion
identities of the homeomorphism identify the resulting families with
the literal original point operations.

`regularAtlasLieGroup G A` proves that any universe-general regular
atlas on these actual points makes the original group a real `C∞`
Lie group. It installs `A.chartedSpace` and `A.isManifold`. For
multiplication it applies `A.contMDiff_iff_regularSmooth` to the
product source, uses smoothness of the two projections to obtain their
regular-function tests, and applies `regularSmooth_mul`. For inversion
the same argument uses the identity family and `regularSmooth_inv`.
The analytic comparison results are imported theorems, so there is
no comparison premise.

`smoothAffineGroupChartedSpace hsmooth` abbreviates exactly the named
`PointManifold.General.smoothAffineChartedSpace hsmooth`.
`smoothAffineLieGroup hsmooth` applies the atlas theorem to exactly
`smoothAffineRegularAtlas hsmooth`; it selects no further atlas.
Its sole smoothness hypothesis is the algebraic property
`hsmooth : SmoothOfRelativeDimension d G.X.hom`.
`smoothAffine_contMDiff_mul` and `smoothAffine_contMDiff_inv`
project the two smoothness fields for these same charts, with the
literal functions `(p,q) ↦ p * q` and `p ↦ p⁻¹`.
The real and complex Lie group theorems specialize to the named chart
aliases, with models `Fin d → ℝ` and `Fin d → ℂ`, whose real
dimensions are `d` and `2 * d`. Constant relative dimension remains
explicit, and zero dimension and empty point spaces are included.

`smoothAffine_contMDiff_iff_coordinateSmooth` composes the named
manifold's intrinsic family criterion with the evaluation comparison
above. The source has real normed model `E : Type v`, chart model
`H : Type v`, model with corners `I`, and carrier `M : Type w`.
The repeated `v` follows the existing `CoordinateSmooth` interface;
the coefficient universe `u` and source carrier universe `w` are
independent. The source needs topology and `ChartedSpace H M`, with
no source manifold premise. The real and complex family theorems
specialize the same result.

Worker 94 internally adapted Worker 1203's implementations in
`AffinePointRegularSmooth`, `AffinePointRegularLieGroup` and
`SmoothAffinePointLieGroup` to the universe-general regular-evaluation,
atlas and named-manifold interfaces. The coordinate-smooth group
preservation proofs, original carrier homeomorphism and evaluation
identities are imported unchanged by Lean name. No external theorem
is newly transcribed. This construction provides no completion
transport, differential growth, measure or reduction theorem.
