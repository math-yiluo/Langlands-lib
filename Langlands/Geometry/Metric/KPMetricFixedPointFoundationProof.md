# The aggregate Kaletha–Prasad metric fixed-point foundation

This module proves the exact published target
`Langlands.Geometry.Metric.KP.MetricFixedPointFoundationStatement.{uX, uG}` from
`KPFixedPointStatement`. Its theorem is
`Langlands.Geometry.Metric.KP.metricFixedPointFoundation`, with the same
independent universe parameters `uX` (metric carriers) and `uG` (acting
groups) as the target.

## Implemented proof

The target is a right-nested conjunction of six statements. The proof is the
anonymous constructor of that conjunction, with one published proof theorem in
each slot. All names are in namespace `Langlands.Geometry.Metric.KP`.

| Conjunct | Proof theorem | Module under `Langlands.Geometry.Metric` | Source |
| --- | --- | --- | --- |
| `GeodesicUniquenessStatement.{uX}` | `geodesicUniqueness` | `KPGeodesicUniquenessProof` | Lemma 1.1.11 |
| `ClosedBallConvexityStatement.{uX}` | `closedBallConvexity` | `KPClosedBallConvexityProof` | corrected Lemma 1.1.13 |
| `ClosedConvexHullStatement.{uX}` | `closedConvexHull` | `KPClosedConvexHullProof` | Definition 1.1.14 and the following paragraph |
| `BarycenterStatement.{uX}` | `barycenter` | `KPBarycenterProof` | Theorem 1.1.15(1) |
| `BoundedSetStabilizerFixedPointStatement.{uX}` | `boundedSetStabilizerFixedPoint` | `KPBoundedSetStabilizerProof` | Theorem 1.1.15(2) |
| `BoundedActionFixedPointStatement.{uX, uG}` | `boundedActionFixedPoint` | `KPBoundedActionFixedPointProof` | Corollary 1.1.19 |

Each component theorem is used at exactly the universe levels the conjunct
requires, and each keeps its own hypotheses: the first three assume an NPC
geodesic space without completeness, the two Theorem 1.1.15 components also
assume completeness, and the Corollary 1.1.19 component assumes completeness
and nonemptiness but no geodesic existence. The conjunction assumes none of its
components as input; every conjunct is discharged by its proof theorem.

The module imports `KPBoundedActionFixedPointProof`, which proves the last
conjunct from `completeNPCGeodesic` and `boundedSetStabilizerFixedPoint`, and
imports the other five component proof modules explicitly. No new lemma is
proved here.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Section 1.1, printed pp.5–7 / PDF pp.36–38, with the authors' corrections of
1 November 2024, `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
Section 1.1, PDF pp.1–2. The aggregate is the interface recorded in
`KPFixedPointStatement`; it makes no mathematical claim beyond its six
components. The paired Markdown of each component proof module describes how
that component is proved.

## Checks

A development `lean_check` of this module in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` reported zero diagnostics. Inspection
of `metricFixedPointFoundation` reported universe parameters `uX` and `uG` and
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. No
external Lean code is adopted.
