# Proof of `MetricRealizationStatement`

This module proves `Langlands.Geometry.Building.MetricRealizationStatement`
(module of the same name) at every universe `u`:

```
theorem Langlands.Geometry.Building.metricRealization :
    MetricRealizationStatement.{u}
```

For every nonarchimedean local field `F`, connected reductive `G/F`,
`P : ParahoricBuildingData G`, realization `R` and splitting `T` satisfying
KP Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6 and 4.1.9, it constructs a
`MetricRealization` of the existing quotient `P.ReducedBuilding`. That is a
metric which is complete and NPC, for which the existing action of `G(F)` is
isometric and its orbit maps are continuous in `rationalPointTopology F G.X`.

## The metric construction

The metric is the distance of Kaletha–Prasad (2023), Proposition 4.2.1. Its
distance function is
`P.toValuationBuildingData.buildingDist R hR.isBuilding`, module
`Langlands.Geometry.Building.ValuationBuildingDistance`. For points `x`, `y` it
chooses a common apartment `g • A(S)`, writes `x = g • [a]` and `y = g • [b]`,
and returns `dist a b` for the Euclidean root metric on `A(S)`
(`apartmentMetricSpace`, module
`Langlands.Geometry.Building.ValuationApartmentMetric`). The chart
independence for an arbitrary pair of points is the corrected argument, not
Proposition 1.5.13. The two points have facets in both apartments, and the
two-facet Tits transport moves one apartment onto the other while fixing both
points. The difference of the charts is then in `N(F)`, which acts
isometrically on `A(S)`. The result `buildingDist_translatedApartmentMap`
says `d (g • [a]) (g • [b]) = dist a b` for every `g`. It gives the
`G(F)`-invariance `buildingDist_smul` and the restriction
`buildingDist_apartmentMap` to `A(S)`.

The remaining properties come from the retraction and the assembly:

| Property | Source | Module |
| --- | --- | --- |
| retractions `ρ_{A,C}` fix `A(S)`, do not increase `d` and preserve the distance from a point of the closure of `C` | Proposition 1.5.24(1), Lemma 4.2.2(3) and the case `x ∈ C̄` of Lemma 4.2.2(2) | `ValuationBuildingRetraction` (`exists_apartmentRetraction`) |
| `d` is a metric | Proposition 4.2.3(1) | `Langlands.Geometry.Metric.RetractionGluing` |
| midpoint NPC inequality | Proposition 4.2.7 | `Langlands.Geometry.Metric.RetractionGluing` |
| completeness | Theorem 4.2.10, Lemma 4.2.11 | `ValuationBuildingCompleteness` |
| isometric action | Proposition 4.2.1 as corrected | `ValuationBuildingMetricAssembly` |
| continuous orbit maps | open stabilizers, as in Proposition 4.2.18 | `ValuationBuildingOrbitContinuity` |

The assembly theorem
`ValuationBuildingData.metricRealizationStatement_of_exists_isRetractionBuildingDistance`
(module `Langlands.Geometry.Building.ValuationBuildingMetricAssembly`) reduces
the statement to a distance `d` satisfying
`IsRetractionBuildingDistance`, namely `G(F)`-invariance, restriction to the
Euclidean metric on `A(S)`, and the retractions above. The metric is
`IsRetractionGluedDistance.metricSpace` with distance function `d` itself, on
the unchanged quotient. No completion or other carrier is used.

## Proof as implemented

`metricRealization` applies the assembly theorem. It then introduces the data
and the seven hypotheses
`hR hB hT hRR hD hC hTits` of the statement, in its order, and constructs
`d` with its three properties.

1. A Tits system. The affine roots form a locally finite reflection
   arrangement (`hD.isAffineRootSystem_affineRoots`). So some point `y` of
   `A(S)` is regular (`exists_regularPoint_closure`, applied to an arbitrary
   point of the nonempty torsor `A(S)`). Its facet is a chamber, and `hTits`
   gives a Tits system `hTy : P.IsBuildingTitsSystem (facet y) π Sgen`. The
   distance lemmas need one such system. Any chamber will do.
2. `hN := hR.normalizerApartmentStabilizer` (the stabilizer of `A(S)` is
   `N(F)`) and `hK := hR.isBuilding` (`R` is a building) are fields of
   `P.SatisfiesBuildingAxiom R`.
3. `d := buildingDist R hK`, with
   * `smul := buildingDist_smul hD hN hC hTy R hK`;
   * `apartmentMap := buildingDist_apartmentMap hD hN hC hTy R hK`;
   * `exists_retraction := exists_apartmentRetraction hcommon hD hN hC hTits
     (buildingDist_translatedApartmentMap hD hN hC hTy R hK)`, where
     `hcommon := R.hasCommonApartmentWith_of_isBuilding hK`.

The hypotheses `hT` (Axiom 4.1.4) and `hRR` (`HasRootReflections`) are not used.
Of the hypotheses that are used:

* `hB` (Axiom 4.1.2) gives continuous orbit maps;
* `hD` (Axiom 4.1.6, V 7 and AS 2–AS 5) gives the root system and the sharp
  fixers, and completeness through the discreteness of `N(F)`-orbits;
* `hC` (AS 6) and `hTits` (Axiom 4.1.9) give facet transport, chart
  independence and the retractions;
* `hR` (Axiom 4.1.1) gives common apartments and the normalizer.

## Independently derived steps

These steps differ from the source route. Each is described in the paired
Markdown of its module.

* The retraction is the action of an element of `G(F)^0` that fixes the
  chamber pointwise. Its independence of the element uses the Tits-system
  transport instead of BL 4 (`ValuationBuildingRetraction`).
* Nonexpansion of the retraction is proved by
  `AffineRootSystem.dist_le_of_forall_mem_facetClosure`, a continuous
  induction along the segment, instead of a finite subdivision of the segment
  into facet closures (`FacetClosureLipschitz`).
* The metric axioms and NPC follow from abstract retraction gluing
  (`RetractionGluing`).
* Completeness uses orbit discreteness for the full group `G(F)`, derived from
  the discreteness of `N(F)`-orbits in `A(S)`, instead of facets near a point
  and Proposition 1.5.13 (`ValuationBuildingCompleteness`,
  `DiscreteOrbitCompleteness`, `AffineRootOrbitDiscreteness`).

Sources: Kaletha–Prasad (2023), Section 4.2, printed pp.168–172 / PDF
pp.199–203, and Proposition 1.5.24, printed p.63 / PDF p.94, read with the
corrections of 1 November 2024, PDF pp.28–29.
