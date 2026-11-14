# Complete NPC metrics on actual maximal-unramified buildings

`Langlands.Geometry.Building.MaximalUnramified.completeNPCMetric` proves the
published proposition
`Langlands.Geometry.Building.MaximalUnramified.CompleteNPCMetricStatement.{u}`
at arbitrary universe `u`.

For every nonarchimedean local field `F`, affine group scheme `G` over the actual
inertia fixed field `K = inertiaFixedField F`, and supplied
`B : MaximalUnramified.BuildingData F G`, it gives `Nonempty B.CompleteNPCMetric`.
This packages a metric on the original `B.ReducedBuilding`, completeness,
nonpositive curvature in the KP midpoint sense, and isometry of the existing
`rationalPoints G` action. It uses the prescribed integer-valued valuation and
the supplied quotient, apartment and action. The group and datum are arbitrary
within the published statement.

The implemented proof is the application

```lean
completeNPCMetricStatement_of_retractionDistance commonApartments retractionDistance
```

All three ingredients are published Library theorems in the
`Langlands.Geometry.Building.MaximalUnramified` namespace:

- `commonApartments`, from `IntegerValuationCommonApartmentsProof`, supplies a
  common translated original apartment for any two quotient points.
- `retractionDistance`, from `UnramifiedRetractionDistanceProof`, supplies an
  invariant function restricting to the apartment root distance, with
  contracting apartment retractions preserving distance from a chosen
  apartment point.
- `completeNPCMetricStatement_of_retractionDistance`, from
  `UnramifiedBuildingMetricReduction`, applies the generic integer-valued
  construction directly to `B`. The construction glues the apartment root
  metric using those retractions, proves nonpositive curvature, proves
  completeness using discrete normalizer orbits, and retains isometry of the
  original rational-point action.

The single import `UnramifiedRetractionDistanceProof` makes these declarations
available through its published imports. No additional hypothesis is supplied
to the target. In particular, the proof requires neither descent of `G` from
`F`, Galois stability of `B`, nor a local-field structure on `K`.

This is an internal composition of the published results above. Their paired
Markdown files document the geometric construction and its provenance in
Kaletha–Prasad Section 4.2, Proposition 7.6.3 and Remark 7.6.5, with the
1 November 2024 corrections. This module adds the unconditional specialization;
it introduces no further source assertion or geometric input. Neither the
vertex-stabilizer maximality conclusion nor a bounded-geometry statement is an
ingredient.
