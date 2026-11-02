# Fixed points of bounded isometric group actions

This module proves the exact published target
`Langlands.Geometry.Metric.KP.BoundedActionFixedPointStatement.{uX, uG}` from
`KPFixedPointStatement`. Its theorem is
`Langlands.Geometry.Metric.KP.boundedActionFixedPoint`, with the two
independent universe parameters `uX` (the metric carrier) and `uG` (the
acting group).

For every nonempty complete metric space `X : Type uX` satisfying the
primitive `IsNonpositivelyCurved X` condition, every group `G : Type uG` with
a Mathlib `MulAction G X` and `IsIsometricSMul G X`, and
`HasBoundedAction X (Set.univ : Set G)`, the theorem produces a point of
`MulAction.fixedPoints G X`. No geodesic, topology, continuity, faithfulness,
compactness or finiteness hypothesis is added.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Corollary 1.1.19 with Lemma 1.1.17 and Definition 1.1.18, printed p.7 /
PDF p.38, and Theorem 1.1.15(2), printed p.6 / PDF p.37. The printed proof
of the corollary is one line: any orbit is nonempty and bounded, so
Theorem 1.1.15(2) applies. The authors' corrections of 1 November 2024,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
Section 1.1, PDF pp.1–2, do not change Corollary 1.1.19. Theorem 1.1.15
assumes a geodesic space, while the corollary does not; the proof below
supplies that missing hypothesis. Both PDFs are under
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/`.

## Implemented proof

All names are in namespace `Langlands.Geometry.Metric.KP`.

1. `HasBoundedAction X univ` unfolds to a point `x : X` whose orbit
   `M = (fun h : G => h • x) '' univ` is bounded. The orbit is nonempty because
   it contains `1 • x = x`.
2. The published theorem `completeNPCGeodesic` from
   `KPCompleteNPCGeodesicProof` turns completeness and the primitive NPC
   condition into `IsGeodesicSpace X`. This discharges the geodesic hypothesis
   of Theorem 1.1.15, which is not a premise of the target.
3. The published theorem `boundedSetStabilizerFixedPoint` from
   `KPBoundedSetStabilizerProof` (KP Theorem 1.1.15(2)), applied to the
   nonempty bounded set `M`, gives one point `b` with `e b = b` for every
   `e : X ≃ᵢ X` satisfying `e '' M = M`.
4. For each `g : G`, Mathlib's `IsometryEquiv.constSMul g` is the bijective
   isometry `y ↦ g • y`; its inverse is the action of `g⁻¹`. The helper
   theorem `constSMul_image_orbit` proves that it maps `M` onto `M`:
   `g • (h • x) = (g * h) • x`, and conversely `h • x` is the image of
   `(g⁻¹ * h) • x`.
5. Therefore `g • b = b` for every `g`, which is membership of `b` in
   `MulAction.fixedPoints G X`.

The fixed point `b` is chosen once, before the group element, so it is a
common fixed point of the whole action. It is the point supplied by the
stabilizer theorem (the barycenter of the closed convex hull of the orbit),
and it need not lie in the orbit. The argument applies only the published
component theorems and the elementary orbit-invariance lemma; it adds no
assumption to the actual action, its bounded orbit or its fixed-point set.
The ambient carrier is not required to share a universe with the group, since
only the induced isometries `X ≃ᵢ X` enter the stabilizer theorem.

## Checks

A development `lean_check` of this module in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` reported zero diagnostics. Inspection
of `boundedActionFixedPoint` reported universe parameters `uX` and `uG` and
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. No
external Lean code is adopted.
