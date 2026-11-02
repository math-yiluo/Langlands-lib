# Actual smooth affine point Lie groups and the family criterion

`Langlands.GroupScheme.smoothAffineGroupManifold.{v,w}` proves the exact
published proposition `smoothAffineGroupManifoldStatement.{v,w}` for every
`RCLike` field `k : Type`, actual affine group scheme `G` over `Spec k`,
and natural number `d`. Its only smoothness input is the algebraic condition
`SmoothOfRelativeDimension d G.X.hom`. The source normed space and model
space in the family criterion have arbitrary universe `v`, and the source
manifold has arbitrary universe `w`.

The proof applies the published `regularChartExistence k G.X d` to that
algebraic input and obtains one atlas `A : RegularAtlas k G.X d`. It uses
`A.chartedSpace` for both conclusions of the target.

For the Lie group conclusion, it applies the published
`regularAtlasLieGroup G A` with
`regularAtlasComparison.{0,0,0} k G.X d`. This comparison supplies the
manifold structure and the regular-function family criterion needed for
the identity map and the two product projections. The helper then transfers
the existing regular-smooth multiplication and inversion results to smooth
group operations. Its group law is the original categorical point group
`G.ringPointGroup (CommAlgCat.of k k)` on `RingPoint k G.X k`.

For the family conclusion, it introduces all the source types, structures,
model with corners, and the family `p` quantified by the target. It applies
`regularAtlas_contMDiff_iff_coordinateSmooth G I A`, using the family
conjunct of `regularAtlasComparison.{v,v,w} k G.X d`. This equates smoothness
of the family transported by the published
`G.affinePointsRingPointHomeomorph (CommAlgCat.of k k)` with
`G.CoordinateSmooth (CommAlgCat.of k k) (RingHom.id k) I p`. The repeated
universe `v` matches the equal universes of the source normed and model
spaces in `CoordinateSmooth`. No comparison or chart hypothesis remains
in the theorem.

The atlas lives on the actual relative-scheme-morphism carrier and uses
its existing global regular-function evaluation topology. The construction
does not change that topology, the point carrier, the categorical group
operations, or the actual-carrier homeomorphism in the family criterion.
There is no positivity or point nonemptiness assumption: the chosen atlas
and the two comparison instantiations also apply when `d = 0` or the point
space is empty.

`realSmoothAffineGroupManifold` and `complexSmoothAffineGroupManifold`
specialize the same theorem to the exact real and complex target
abbreviations. Their real models are respectively `Fin d → ℝ` and
`Fin d → ℂ`; the published `real_model_finrank` and
`complex_model_finrank` in `RegularCharts` identify the real dimensions as
`d` and `2 * d`.

This is an internal composition of the published algebraic chart-existence
proof, analytic atlas-comparison proof, and group transport helpers. The
algebraic prerequisite constructs charts from standard-smooth principal
neighborhoods, while the analytic prerequisite proves smooth chart changes
and tests families by global regular evaluations. This file reuses those
results by Lean name and proves the group existence target without changing
its statement or its imported definitions. Author: Worker 135.
