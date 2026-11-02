# KP Lemma 1.1.13: closed-ball convexity

This module proves the exact published `ClosedBallConvexityStatement` in
`Langlands.Geometry.Metric.KP`, in every carrier universe. A closed ball with
real radius `r ≥ 0` is nonempty because it contains its center, and contains
every normalized geodesic between any two of its points. Radius zero is retained.
No completeness or local compactness is used.

The helper `IsGeodesic.dist_le_max_endpoints` bounds the distance to a fixed
point along a geodesic by the larger endpoint distance. The implemented proof
uses the extreme value theorem on the compact parameter interval `[0,1]` in
place of the source's dyadic subdivision argument. This compactness concerns
the parameter interval alone and imposes no compactness assumption on `X`.

For distinct endpoints, a maximum cannot occur at an interior parameter `t`.
Choose the two parameters `t ± ε` with `ε = min(t,1-t) > 0`. Their restricted
geodesic has midpoint `γ t`; the previous module shows that it satisfies the
primitive NPC inequality. Maximality bounds both terms on the right by the
square of the maximum distance. The inequality forces the distance between
the two restricted endpoints to be zero, contradicting the constant-speed law
and their distinct parameters. Thus the maximum occurs at an endpoint.
For coincident endpoints the published constant-geodesic law proves the bound.
The closed-ball conclusion follows by bounding both endpoint distances by `r`.

The NPC midpoint fact is imported from `KPGeodesicUniquenessProof`; no convexity
conclusion is used as an assumption. The geodesic-space premise of the published
target is preserved, although the pointwise helper concerns each given geodesic
and needs only NPC.

Sources: Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Lemma 1.1.13, printed pp.5–6 / PDF pp.36–37; and the authors' corrections of
1 November 2024, `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.1. The corrections require nonempty convex sets and an ambient geodesic
space. The maximum argument is an internal derived proof of this same result.
