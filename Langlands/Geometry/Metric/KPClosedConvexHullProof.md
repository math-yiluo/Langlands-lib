# Closed bounded geodesic convex hull

This module proves the exact published `ClosedConvexHullStatement` in namespace
`Langlands.Geometry.Metric.KP`, for metric spaces in every carrier universe.
Given a nonempty bounded subset `M` in an NPC geodesic space, its published
`closedGeodesicConvexHull M` is closed, bounded, geodesically convex in the
nonempty sense, and contains `M`. No completeness or local compactness is assumed.

Choose `z ∈ M`. Boundedness gives a real radius `r` with `M ⊆ closedBall z r`.
Because this ball contains `z`, its radius is nonnegative, including the possible
case `r = 0`. The exact ball-convexity theorem from `KPClosedBallConvexityProof`
therefore supplies a closed bounded convex superset of `M`.

Apply the published intrinsic hull boundedness law to this actual superset.
The other three clauses are the published intrinsic hull laws: intersections of
closed sets are closed; an intersection of geodesic-containing sets contains all
such geodesics and is nonempty because it contains `M`; and each defining set
contains `M`. Thus the proof discharges the superset-existence obligation rather
than assuming it or replacing the specified intersection by a different hull.

Sources: Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Definition 1.1.14 and the following paragraph, printed p.6 / PDF p.37; and the
authors' corrections of 1 November 2024, `kaletha-prasad-2024-corrections`,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.1. The correction calls item 1.1.14 a remark; the book labels it a
definition. The corrected ambient geodesic-space hypothesis and corrected
nonempty convexity convention are preserved exactly.

The imported proof chain establishes KP Lemmas 1.1.11 and 1.1.13 from primitive
NPC. This module follows the source's hull argument and introduces no additional
mathematical assumption. Barycenter and fixed-point theorems remain outside its
scope.
