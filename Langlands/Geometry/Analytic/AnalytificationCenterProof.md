# Surjectivity and rational fibres of the analytification center maps

`Langlands.Analytic.SchemeAnalytification.analytificationCenter` proves
`AnalytificationCenterStatement.{u,v}` for a complete, ultrametric,
nontrivially normed field `K : Type u`. It covers finite polynomial
presentations of commutative `K`-algebras `A : Type v` and schemes
`X : Scheme.{u}` locally of finite type over `K`.

## Affine center map

For a prime `p` of `A`, `center_surjective_of_finiteType_norms` applies
`finiteTypeDomainNormExtension.{u,v}` to the finite-type domain `A / p`.
It pulls the resulting faithful seminorm back to `A`, where the seminorm
extends the norm of `K` and has kernel `p`. The range identity
`SeminormComparison.range_pointSeminorm` realizes this seminorm as an
analytic point with center `p`.

At the analytic point of a `K`-algebra map `φ : A → K`, the seminorm has
value `‖φ a‖` on `a`. Thus `mem_center_analyticPoint` identifies its center
ideal with `ker φ`. If another analytic point has the same center, its
seminorm vanishes on `a − algebraMap K A (φ a)` for every `a`. The triangle
inequality in both directions and agreement on the scalars force its value
on `a` to be `‖φ a‖`. The proof supplies `pointSeminorm_injective` to
`eq_analyticPoint_of_center_eq` to turn equality of seminorms into equality
of points.

## Scheme center map

Every point of `X` lies in an affine open `U`. The scheme surjectivity
helper sends a preimage under the affine center map of `U` into the glued
space via `ι K f U`. The proof supplies affine surjectivity for each chart
using the same seminorm argument and `finiteTypeDomainNormExtension.{u,u}`,
since chart coordinate rings are in universe `u`.

`OpenGluing.range_ι` identifies the preimage of `U` under the scheme center
map with the range of `ι K f U`. Its principal-open range formula identifies
restriction to a basic open with localization, whose analytic image is
the locus where the defining section has nonzero seminorm. For an analytic
point with center in `U`, a principal neighborhood of the center in a
representing affine chart can be chosen inside `U`, and the chart maps
agree there.

`CenterComparison.center_analyticRationalPoint` computes the center on the
chosen affine chart using the affine kernel formula and sends it into `X`,
giving `p.left (IsLocalRing.closedPoint K)`. For a point with this center,
the chart range identity places it in that same affine chart. Injectivity
of the map from the chart's prime spectrum into `X` gives equality of
the affine centers. `CenterComparison.eq_analyticRationalPoint_of_center_eq`
then uses the affine singleton-fibre argument and maps the equality into
the glued space.

## Provenance

The theorem assembles the Library's center comparisons, seminorm realization,
faithful norm extension and principal-open range results. Berkovich's
*Spectral Theory and Analytic Geometry over Non-Archimedean Fields* (1990),
Theorem 3.4.1(i), proof steps (2)–(3), and Remark 3.4.2 (printed pp. 63–64,
PDF pp. 77–78) give the surjectivity, open restriction and affine seminorm
description. The rational-fibre clauses use the resulting description of
the kernel of the evaluation seminorm. The target's companion records the
original source locations and how they apply to the Library's constructions.
[AnalytificationCenterStatement.md](AnalytificationCenterStatement.md)
