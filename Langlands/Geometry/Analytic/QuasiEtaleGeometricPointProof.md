# Geometric points are points of the quasi-étale site

`QuasiEtaleSite.geometricPoint` proves the published
`QuasiEtaleSite.GeometricPointStatement.{u, v, uL}`. For every complete
ultrametric normed ground field `K`, every complete, ultrametric,
algebraically closed normed field `L` with `NormedAlgebra K L`, and every
`L`-valued point `x` of `X : LocalizedCategory.{u, v, v} (K := K)`, the
category of elements of `pointFibre L x` is cofiltered and every covering
sieve for `quasiEtaleTopology X` acts jointly surjectively on that fibre
functor. The ground field, space, and point field universes are independent
as in the target. No nontriviality of the norm, compactness, or separation
of `X` is assumed.

## Implemented proof

The Lean proof supplies the three site-level premises of
`geometricPointStatement_of_geometry`:

- `geometricPointRefinement`: replace each of two pointed objects by a
  compact chart domain with a single domain–étale factorization over `X`.
  The common map of their analytic fibre product again has such a
  factorization, and preservation of the pullback on full field points
  gives the compatible point of the resulting site object.
- `geometricPointEqualization`: restrict a pointed source chart to the
  intersection of the inverse images of a compact target chart under the
  two parallel maps. The full images agree in that chart by injectivity
  for its inclusion. Their pair in the self-pullback over `X` agrees with
  the diagonal at the field point. Restrict to the inverse image of the
  compact chart's diagonal domain, where the maps agree. The restrictions
  retain a domain–étale factorization and the chosen field point.
- `geometricPointImageLift`: for a site arrow `V ⟶ U`, the composite to
  `X` is the quasi-étale structure map of `V`. At a chosen ordinary
  preimage, a finite chart in a local étale envelope supplies a full
  point over a field algebraic over a base-chart residue field. The
  completed residue field of a chart at the intermediate point embeds
  between those fields. Extend its prescribed isometric embedding into
  `L` across that algebraic extension. This lifts the full point of `U`,
  not only its ordinary point.

The reduction uses `(X, 𝟙 X, x)` for nonemptiness and the first two inputs
for the two cone axioms. A generating cover contains an arrow whose image
contains the ordinary point of the prescribed fibre element. The third
input lifts that element, and the overcategory triangle keeps the lift
over `x`. Cofilteredness supplies pointwise lifting squares; the published
`PointwiseCovering` argument uses them to pass from the generating
precoverage to **all** covering sieves of the generated topology. These
are precisely the two assertions of `PointAxioms L x`, so the result may
be used with `QuasiEtaleSite.toPoint`.

## Source and scope

This is the derived quasi-étale analogue of the étale geometric-point
construction identified in `QuasiEtaleGeometricPointStatement.md`. The
local geometry and covering convention come from Berkovich,
*Vanishing cycles for formal schemes*, Invent. Math. **115** (1994), §3,
printed pp. 543–544; the residue-field method is motivated by Berkovich,
*Étale cohomology for non-Archimedean analytic spaces*, Publ. Math. IHÉS
**78** (1993), §1.4 and Theorem 3.4.1. The Lean route uses compact local
products and diagonals and a pointed algebraic residue witness. It does
not assume global quasi-étale composition, base change, or right
cancellation, nor assert those stability theorems or conservativity of
a family of points.
