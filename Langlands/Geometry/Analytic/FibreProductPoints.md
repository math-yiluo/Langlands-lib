# Compatible points of the glued analytic fibre product

Author: Worker 621.

This module extends the existing affinoid compatible-point lifting theorem
to the glued fibre-product chart system, then to the constructed analytic
fibre product of Hausdorff saturated atlas presentations. It is an internal
consequence of the Library's actual chart, domain, and pushout constructions.

## Charts containing compatible points

`IndexedAffinoidAtlas.exists_chart_at` says that every point belongs to an
atlas chart. The proof uses the covering property of the atlas's net.

For compatible strong maps `f : A → C` and `g : B → C`,
`FibreProduct.exists_pair_of_compatible_points` assumes that both source
atlases contain all local domains. For points `x` and `y` having the same
image in `C`, it produces a `PairIndex f g` whose two source charts contain
the prescribed points.

The proof starts with arbitrary charts at `x` and `y`, and the target
charts selected by the two maps. The net intersection property supplies a
common smaller base chart at their common image. Taking its inverse
image in each original source chart gives two actual local domains.
Closure under all local domains realizes both as source atlas charts.
Their images lie in the common base chart, as required for a pair index.
No Hausdorff hypothesis is used in this argument.

## Lifting to the glued space

`FibreProduct.exists_point` lifts the same compatible points to a point
of `(FibreProduct.chartSystem f g).Space`. In the chart pair just found,
the point coordinates have identical images in the base chart spectrum:
the base chart's injectivity and the strong-map chart equations prove this.
The published theorem `AffinoidPushout.exists_point` then supplies a point
of the actual affinoid pushout with both prescribed projections. Its
image in the glued chart system gives the required lift.

`FibreProduct.pointLift` chooses such a point, with its two projections
recorded by `fst_pointLift` and `snd_pointLift`. The lifting existence and
the chosen lift have no Hausdorff hypothesis.

`SaturatedAtlasPresentation.exists_fibreProduct_point` specializes this
to the existing analytic fibre product `fibreProduct f g` and its actual
projection maps. Here the three saturated presentations have Hausdorff
underlying spaces and all universes equal to the coefficient-field
universe, as required by the existing analytic fibre-product construction.
The proof uses the compatible-map representatives and their definitionally
unchanged underlying point maps.

## Provenance and scope

The argument is derived from the Library's atlas net, local-domain
closure, `FibreProduct.exists_chart_preimage`, the injectivity of chart
maps, and `PresentedAffinoidAlgebra.AffinoidPushout.exists_point`. It
introduces no new external literature assertion.

This proves surjectivity onto compatible pairs of underlying points,
without asserting uniqueness of the lift. It does not prove the
categorical universal property of the analytic fibre product, étaleness
of its projections, or pointwise lifting in the unrestricted localized
analytic étale site. Those additional geometry and universe obligations
are still needed to apply the categorical covering-points reduction to
that site.
