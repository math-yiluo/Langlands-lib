# Analytic manifolds of actual smooth affine points over complete fields

Author: Worker 115, adapting constructions of Workers 274, 94, 362, 135, 1650,
383 and 1659.

For every affine `X : Over (Spec (CommRingCat.of k))` and every natural `d`,
`smoothAffineRegularAtlas k X d h` constructs a regular analytic atlas from
its sole additional premise `h : SmoothOfRelativeDimension d X.hom`.
`smoothAffineChartedSpace` names the resulting charts on the actual carrier;
it is supplied explicitly and does not install a global instance.
`smoothAffineIsManifold` proves analytic regularity over the original field.

The construction applies the principal-open standard-smooth covering reduction
to the pointwise charts obtained from finite submersive presentations.
The dependent Jacobian is an evaluated unit. Analytic polynomial evaluation
has a strict derivative over every nontrivially normed field, so the strict
inverse function theorem gives ambient local inverses over the complete field.
Restricting to the zero fibre gives the analytic charts. Their coordinates
are regular fractions, and inverse evaluation of every regular function is
analytic. Denominator clearing transfers the charts through principal opens.

`RegularAtlasComparisonProof` proves analytic transition maps, manifold
assembly and the regular-function criterion.
`smoothAffine_contMDiff_regularEvaluation` specializes this criterion's
evaluation result to the chosen atlas.
`smoothAffine_contMDiff_postcomp` gives analytic functoriality for every
actual relative affine scheme morphism; the dimensions may differ.
The imported `RegularAtlasFunctoriality` also supplies analytic isomorphism
maps and identity diffeomorphisms comparing any two regular atlases.

This is an internal prerequisite construction for Conrad's Proposition 5.4
analytic-manifold assertion (registered source
`conrad-2011-weil-grothendieck-adelic-points`, printed pp.15–16). It adapts the
published `PointManifold.General` algebraic and real-smooth construction,
while leaving every published file unchanged. It now covers arbitrary complete
nontrivially normed fields and analytic regularity over the original field.
It constructs manifolds only on smooth affine schemes. Analytic local
isomorphisms for etale maps, charts on nonaffine schemes or algebraic spaces,
and the exact `AnalyticPointManifoldStatement` are further obligations.

Throughout this module, `k : Type u` is an arbitrary complete nontrivially
normed field, the scheme is affine over `Spec k`, and its actual point carrier
is `PointTopology.RingPoint k X k` with its published evaluation topology.
The analytic order is `ω` over `k`. There is no characteristic, archimedean,
positive-dimension or point-nonemptiness assumption.
