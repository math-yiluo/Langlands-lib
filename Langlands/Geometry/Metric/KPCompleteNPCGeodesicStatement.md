# Geodesic existence in complete NPC metric spaces

The declaration `Langlands.Geometry.Metric.KP.CompleteNPCGeodesicStatement`
is a proposition stating that every complete metric space satisfying the
published primitive `IsNonpositivelyCurved` condition is a geodesic space.
The metric-space carrier has arbitrary universe `uX`. There is no
nonemptiness, local compactness, properness or geodesic-existence premise.
An empty metric space satisfies the conclusion vacuously.

The only import is `Langlands.Geometry.Metric.KPDefinitions`. The conclusion
uses its `IsGeodesicSpace`: each ordered endpoint pair is joined by a
continuous Mathlib path satisfying the normalized constant-speed distance
law for every pair of unit-interval parameters. The imported module proves
that this condition agrees with the literal KP curve-length definition.

## Derived provenance

This is an internal derived construction target, rather than a separately
numbered assertion attributed to Kaletha–Prasad. Its source definitions are:

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
  Definitions 1.1.2, 1.1.4 and 1.1.8, printed p.4 / PDF p.35.
- The authors' corrections of 1 November 2024,
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
  Section 1.1, PDF pp.1–2. These retain the primitive midpoint condition
  and require the ambient geodesic hypothesis for the ball and hull results.

Both registered originals are in
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/`.

The reason for isolating this consequence is that the published target for
Corollary 1.1.19 has completeness and NPC as hypotheses, while the published
Theorem 1.1.15 targets also assume geodesic existence. Proving this statement
will discharge that premise without changing either source target.

The anticipated derivation uses the following elementary construction.
The NPC midpoint inequality, evaluated at each endpoint and combined with
the triangle inequality, gives a metric midpoint with both distances equal
to half the endpoint distance. The imported `IsNPCMidpoint.dist_left` and
`IsNPCMidpoint.dist_right` already prove these equalities. Repeatedly insert
such midpoints into compatible dyadic subdivisions of any endpoint pair.
The triangle inequality along a subdivision gives the upper distance
bound; the endpoint triangle inequality gives the matching lower bound.
Thus the resulting map on dyadic parameters satisfies the exact
constant-speed distance law. Completeness extends this uniformly
continuous map from the dense dyadic parameters to the whole unit
interval, preserving that distance law and both endpoints. Coincident
endpoints also admit the constant path. This paragraph explains the
derived target's mathematical rationale; it is not a claim that this
construction has been implemented here.

## Scope

This file defines a proposition and proves no theorem. It adds no axiom,
does not strengthen the NPC predicate, and does not edit the existing
fixed-point statement pair or its imports. It claims neither uniqueness of
geodesics nor a barycenter or fixed-point theorem. A later independent
proof must construct the required paths. Building existence, completeness,
nonpositive curvature and all KP program release gates remain separate
obligations.
