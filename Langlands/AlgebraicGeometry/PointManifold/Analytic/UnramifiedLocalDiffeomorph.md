# Analytic local isomorphisms for unramified affine maps in equal dimensions

Author: Worker 115.

Let `k : Type u` be any complete nontrivially normed field. Let `X` and `Y`
be actual affine schemes over `Spec k`, let `d : ℕ`, and supply regular analytic
atlases of dimension `d` on their actual relative-point carriers with the
published point topologies. No algebraic smoothness is needed in the
atlas-level construction beyond the existence of the supplied atlases.

`RegularChart.coordinateDerivativeEquiv` makes the derivative of a formally
unramified relative morphism in two overlapping charts a continuous linear
equivalence. The preceding module proves it injective; the source and target
are the same finite-dimensional model, so it is surjective. Completeness of
the coefficient field supplies continuity of the linear inverse.

`coordinateDiffeomorphData` constructs a partial analytic diffeomorphism in
those coordinates, containing the specified model point, agreeing everywhere
as a forward function with the coordinate map and having source inside the
chart overlap. Analyticity gives a strict derivative, so the general strict
inverse function theorem supplies an open partial homeomorphism. It is
restricted to the overlap's interior; the specified point remains in the
source by continuity of the actual point map. At every point of the restricted
source, analyticity and the derivative equivalence hold again. The analytic
inverse theorem applied there proves its inverse analytic throughout its
target. The coordinate models have no boundary.

`RegularAtlas.chartPartialDiffeomorph` packages a selected atlas chart as a
partial analytic diffeomorphism, using the already established manifold
property. `isLocalDiffeomorph_postcomp` composes the source chart, the coordinate
partial diffeomorphism and the inverse target chart. The overlap conditions
and inverse equations prove that its forward map agrees on its source with
actual postcomposition by `f`. This establishes `IsLocalDiffeomorph` for every
formally unramified relative morphism between the two equal-dimensional atlases.

`smoothAffine_isLocalDiffeomorph_etale` applies this construction to the atlases
chosen solely from `SmoothOfRelativeDimension d X.hom` and the corresponding
hypothesis for `Y`, and to every `Etale f.left`. Thus the local analytic
isomorphism assertion holds for the constructed smooth affine manifolds.
Zero dimension and empty actual point spaces are included.

This is an internal prerequisite construction for Task 5259, which proves
Conrad Proposition 5.4's analytic-manifold assertion (registered source
`conrad-2011-weil-grothendieck-adelic-points`, printed pp.15–16). Its implemented
route uses evaluation derivations and formal unramifiedness to establish the
invertible derivative, then the analytic inverse theorem. It uses the analytic
affine-manifold construction by import and changes none of its files.
Transport to nonaffine schemes and algebraic spaces, affine-space normalization
and the exact `AnalyticPointManifoldStatement` remain further obligations.
