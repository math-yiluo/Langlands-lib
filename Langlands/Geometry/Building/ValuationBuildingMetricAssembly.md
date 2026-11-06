# Assembling a metric realization from apartment retractions

This module reduces `Langlands.Geometry.Building.MetricRealizationStatement`
to one geometric input: a distance function on the existing quotient
`B.ReducedBuilding` with the properties that Kaletha–Prasad (2023), Section 4.2,
establish for their building distance. Everything else in the metric
realization is proved from it. The metric, its completeness, the
nonpositive curvature, the isometric action and the continuity of orbit maps
all come from earlier modules. The module does not construct such a distance
or its retractions.

## Declarations

All names are in the namespace `Langlands.Geometry.Building.ValuationBuildingData`.
Throughout, `A(S) = B.Apartment` carries the Euclidean root metric
`apartmentMetricSpace` of `Langlands.Geometry.Building.ValuationApartmentMetric`,
installed through local instances, and `[a]` denotes `B.apartmentMap a`.

| Lean name | Kind | Content |
| --- | --- | --- |
| `IsRetractionBuildingDistance B d` | structure (`Prop`) | Hypotheses on `d : B.ReducedBuilding → B.ReducedBuilding → ℝ`, see below |
| `IsRetractionBuildingDistance.smul_apartmentMap` | theorem | `d (g • [a]) (g • [b]) = dist a b` |
| `IsRetractionBuildingDistance.injective_smul_apartmentMap` | theorem | `a ↦ g • [a]` is injective |
| `IsRetractionBuildingDistance.isRetractionGluedDistance` | theorem | Given common apartments, `d` and the translated apartments `{Y | B.IsApartment Y}` satisfy `Metric.KP.IsRetractionGluedDistance` |
| `nonempty_metricRealization_of_isRetractionBuildingDistance` | theorem | `Nonempty B.MetricRealization` from such a `d` |
| `metricRealizationStatement_of_exists_isRetractionBuildingDistance` | theorem | `MetricRealizationStatement.{u}` if every datum satisfying its hypotheses admits such a `d` |

The fields of `IsRetractionBuildingDistance B d` are:

| Field | Statement | Source |
| --- | --- | --- |
| `smul` | `d (g • x) (g • y) = d x y` for all `g ∈ G(F)` | Proposition 4.2.1 as corrected ("which is G-invariant and") |
| `apartmentMap` | `d [a] [b] = dist a b` | Proposition 4.2.1: `d` restricts to the Euclidean metric `d_A` on the apartment `A(S)` |
| `exists_retraction` | for every `a ∈ A(S)` there is `ρ : B(G) → A(S)` with `ρ [b] = b`, `dist (ρ x) (ρ y) ≤ d x y` and `dist a (ρ x) = d [a] x` | the retraction `ρ_{A,C}` of Proposition 1.5.24 for a chamber `C` of `A(S)` whose closure contains `a`, with Lemma 4.2.2(2),(3) |

The structure is a derived interface. KP define `d` by Proposition 4.2.1 and
then prove Lemma 4.2.2. Here these properties are hypotheses on an arbitrary `d`.
Only the base apartment `A(S)` and the centre point `a` are recorded, not the
chamber `C`. The Euclidean metric is the root metric
`apartmentMetricSpace`. It is invariant under `N(F)`
(`apartment_normalizer_isometry`), as KP require of the compatible system of
metrics at the start of Section 4.2. No symmetry, positivity or triangle
inequality is assumed for `d`. These are derived.

The theorem `nonempty_metricRealization_of_isRetractionBuildingDistance` has
the hypotheses `hB : B.HasBoundedOpenStabilizers` (Axiom 4.1.2),
`hcommon : ∀ x, B.HasCommonApartmentWith x`,
`hD : B.SatisfiesApartmentAxioms` (V 7 and AS 2–AS 5, Axiom 4.1.6) and
`hd : B.IsRetractionBuildingDistance d`.

## Proofs as implemented

*Gluing.* `isRetractionGluedDistance` checks the three clauses of
`Metric.KP.IsRetractionGluedDistance` (module
`Langlands.Geometry.Metric.RetractionGluing`) for the family of translated
apartments `g • A(S)`:

* common apartments are `hcommon`;
* `g • A(S)` is rewritten as the range of `a ↦ g • [a]` (`Set.smul_set_range`).
  This map is injective, because `g • [a] = g • [b]` gives
  `dist a b = d (g • [a]) (g • [a]) = dist a a = 0`. Along it, `d` pulls back
  to the Euclidean metric by `smul` and `apartmentMap`. The apartment is NPC
  (`apartment_nonpositivelyCurved`), so
  `Metric.KP.exists_apartmentMetric_of_injective` gives the apartment clause;
* for an apartment `g • A(S)` and a centre `g • [a]`, take the retraction
  `ρ` for `a` and use `x ↦ g • [ρ (g⁻¹ • x)]`. It takes values in `g • A(S)`
  and is the identity there. It does not increase `d`, because
  `d (g • [ρ (g⁻¹ x)]) (g • [ρ (g⁻¹ y)]) = dist (ρ (g⁻¹ x)) (ρ (g⁻¹ y)) ≤
  d (g⁻¹ x) (g⁻¹ y) = d x y`. It preserves the distance from `g • [a]`:
  `d (g • [a]) (g • [ρ (g⁻¹ x)]) = dist a (ρ (g⁻¹ x)) = d [a] (g⁻¹ x) =
  d (g • [a]) x`.

*Assembly.* `nonempty_metricRealization_of_isRetractionBuildingDistance` takes
the metric `IsRetractionGluedDistance.metricSpace` with distance `d`. Its
fields are filled as follows:

* `nonpositivelyCurved`: `IsRetractionGluedDistance.isNonpositivelyCurved`,
  KP Proposition 4.2.7. The metric axioms are KP Proposition 4.2.3(1);
* `isometric`: `Isometry.of_dist_eq` applied to `smul`;
* `complete`: `completeSpace_of_isometry_apartmentMap_of_satisfiesApartmentAxioms`
  (module `Langlands.Geometry.Building.ValuationBuildingCompleteness`, KP
  Theorem 4.2.10), with the apartment map an isometry by `apartmentMap`;
* `continuous_orbit`: `continuous_orbit_of_hasBoundedOpenStabilizers` (module
  `Langlands.Geometry.Building.ValuationBuildingOrbitContinuity`). Its proof
  uses only the openness of stabilizers in Axiom 4.1.2, as in the proof of KP
  Proposition 4.2.18. The topology on `G(F)` is
  `rationalPointTopology F G.X`, the same as in `MetricRealization`.

*The statement.* `metricRealizationStatement_of_exists_isRetractionBuildingDistance`
introduces the data and the seven hypotheses of `MetricRealizationStatement`,
in its order. It obtains `d` from the hypothesis `h` and applies the previous
theorem to `P.toValuationBuildingData`. The common apartments come from
`hasCommonApartmentWith_of_isBuilding` (module
`Langlands.Geometry.Building.CommonApartmentConstruction`) applied to the
`isBuilding` field of `P.SatisfiesBuildingAxiom R`. The bounded-open-stabilizer
and apartment-axiom hypotheses are passed on unchanged. The remaining
hypotheses are not used in this reduction. They are available to `h`.

Sources: Kaletha–Prasad (2023), Section 4.2 opening, Proposition 4.2.1,
Lemma 4.2.2, Propositions 4.2.3(1) and 4.2.7, Theorem 4.2.10 and
Proposition 4.2.18, printed pp.168–175 / PDF pp.199–206, and
Proposition 1.5.24 for the retractions, printed p.63 / PDF p.94. These are read with the
corrections of 1 November 2024, Section 4.2, PDF pp.28–29, which add
Axiom 4.1.6 to the standing assumptions and G-invariance to Proposition 4.2.1.

Author: Worker 1221.
