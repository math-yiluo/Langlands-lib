# The complete invariant NPC metric on the maximal-unramified building

This module proves the published proposition
`Langlands.Geometry.Building.UnramifiedBuildingMetricStatement.{u}` (module
`Langlands.Geometry.Building.UnramifiedBuildingMetricStatement`) at an arbitrary
universe `u`:

    theorem unramifiedBuildingMetric : UnramifiedBuildingMetricStatement.{u}

## What is proved

Let `F` be a nonarchimedean local field and `K = inertiaFixedField F`. Let `G` be a
connected reductive group over `F` and `T → G` a torus whose base change is a maximal
split torus over `K`. Let `D` be a Galois-stable KP apartment datum over `K` for the
prescribed valuation, and `C` a centralizer datum that is `ω`-compatible with `D`.
Then the reduced building of the semilinear datum
`UnramifiedBuildingDescent.semilinearData` built from these inputs has a
`MetricRealization`. That is, the existing quotient `B.ReducedBuilding` carries a
metric with the following properties:

- it is complete;
- it is nonpositively curved (`Metric.KP.IsNonpositivelyCurved`);
- the rational points `G(K)` act by isometries;
- every coefficient automorphism `σ ∈ Aut(K/F)` acts by an isometry.

The theorem adds no hypothesis, and it keeps the quotient, actions and data of the
statement unchanged.

## The proof

The proof is a single term. It applies three published Library theorems:

1. `unramifiedBuildingMetricReduction : UnramifiedBuildingMetricReductionStatement.{u}`
   (module `UnramifiedBuildingMetricReduction`). It proves the implication

       MaximalUnramified.CommonApartmentsStatement.{u} →
         MaximalUnramified.RetractionDistanceStatement.{u} →
           UnramifiedBuildingMetricStatement.{u}.

   It glues the Euclidean root metrics of the translated apartments along the
   retraction distance, using the published retraction-gluing interface
   (KP Propositions 4.2.3 and 4.2.7). It proves completeness from discreteness of
   the normalizer orbits and the published discrete-orbit completeness criterion
   (KP Lemma 4.2.11 and Theorem 4.2.10). The coefficient isometries come from the
   Galois invariance of the root-sum distance. The paired Markdown of that module
   explains each step.
2. `MaximalUnramified.commonApartments : CommonApartmentsStatement.{u}`
   (module `IntegerValuationCommonApartmentsProof`). Any two points of the supplied
   quotient lie in a common translated apartment `g • range B.apartmentMap`.
3. `MaximalUnramified.retractionDistance : RetractionDistanceStatement.{u}`
   (module `UnramifiedRetractionDistanceProof`). Every supplied building datum over
   `K` carries a `G(K)`-invariant function `d` that restricts to the Euclidean root
   distance on the apartment and, for every apartment point `a`, admits a retraction
   onto the apartment fixing it, not increasing `d`, and preserving the distance
   from `a` (KP Proposition 4.2.1 as corrected and Lemma 4.2.2).

Applying the reduction to the two premises gives the target. Inspection reports only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Excluded ingredients

The task forbids proofs of `UnramifiedTwistedChamberStatement`,
`UnramifiedTwistedFixedPointStatement` and the `LocalSimplyConnected*` cocycle and
chamber statements, which are downstream consumers of this metric. A scan of the
4326-module Langlands import closure of this module finds none of these names. The
only matches for `UnramifiedBuildingMetricStatement` are the statement module itself,
its conditional reduction and this module.
