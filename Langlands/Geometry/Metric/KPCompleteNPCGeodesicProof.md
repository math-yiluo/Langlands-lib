# Geodesics from completeness and the primitive NPC inequality

The theorem `Langlands.Geometry.Metric.KP.completeNPCGeodesic` proves the exact
published `Langlands.Geometry.Metric.KP.CompleteNPCGeodesicStatement.{uX}`.
For any metric space `X : Type uX`, completeness and the primitive
`IsNonpositivelyCurved X` condition imply `IsGeodesicSpace X`. Every ordered
endpoint pair admits a continuous Mathlib path with

```text
dist (gamma s) (gamma t) = dist x y * |(s : Real) - (t : Real)|.
```

There is no nonemptiness, properness, local compactness, or geodesic premise.
The proof works without dividing by `dist x y`, including coincident endpoints.
The conclusion for an empty carrier is vacuous.

## Sources and derived provenance

This is an internal consequence of the published definitions, rather than a
separately numbered assertion or a proof attributed to Kaletha–Prasad.
The normative source definitions are Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Definitions 1.1.2, 1.1.4 and 1.1.8, printed p.4 /
PDF p.35. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
file `Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023.pdf`.

The authors' *Corrections and additions*, version of 1 November 2024,
Section 1.1, PDF pp.1–2, are registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
file `Kaletha-Prasad--Corrections and additions to Bruhat-Tits theory, a new approach--2024.pdf`.
Both originals are retained in
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/`.
The corrections restore separate ambient geodesic hypotheses for the convex-ball
and hull discussion; they do not include geodesic existence in the primitive
midpoint predicate. The imported `KPDefinitions` supplies the original
definitions and their normalized-path/source-length comparison.

The implemented proof uses a closed distance-coordinate image in place of the
explicit dyadic subdivision anticipated in the statement's rationale.
Its only imports are the published target module and Mathlib's
`Topology.Order.Monotone`; it does not use any fixed-point or barycenter result.

## Implemented proof

Fix endpoints `x,y` and put `D = dist x y`. Consider the triangle-equality locus

```text
M = {p | dist x p + dist p y = D}.
```

The first lemma, `dist_eq_abs_sub_of_dist_add_eq`, proves that any `p,q` in this
locus satisfy

```text
dist p q = |dist x p - dist x q|.
```

The reverse triangle inequality gives the lower bound. For the upper bound,
suppose the separation were strictly larger. Take a primitive NPC midpoint `m`
of `p,q` and apply its squared inequality at `x` and `y`. Writing
`a = dist x p`, `b = dist x q`, the strict separation would imply

```text
dist x m < (a+b)/2,
dist m y < ((D-a)+(D-b))/2.
```

Adding contradicts the triangle inequality for `x,m,y`. This argument assumes
no pre-existing geodesic.

Next, `IsNPCMidpoint.dist_add_eq_and_dist_eq_mean` treats an NPC midpoint
between points of `M` ordered by their distance from `x`. The preceding
distance formula and the published midpoint half-distance equalities, together
with the triangle inequalities, give both membership in `M` and

```text
dist x m = (dist x p + dist x q)/2.
```

The locus `M` is closed because its defining distance sum is continuous, and
therefore is complete. The coordinate `f : M -> Real`, `f p = dist x p`,
is an isometry by the first lemma. Mathlib's
`Isometry.isClosedEmbedding` consequently shows that its range is closed.
That range contains `0,D` and is closed under arithmetic means by the second
lemma, interchanging endpoints when their coordinates have the opposite order.

The private real-order lemma `Icc_subset_of_isClosed_of_mean_mem` shows that
such a range contains `[0,D]`. If a parameter `t` were missing, take the
supremum of the range below `t` and the infimum of the range above `t`.
Closedness places both extremal endpoints in the range. Their arithmetic
mean also belongs to the range, contradicting one of the two extremal
properties. This establishes `exists_dist_eq_of_complete_npc`, which supplies
a point of `M` at every distance in `[0,D]`.

Finally, for each `t` in the unit interval, choose a point `c t` whose distance
from `x` is `t*D`. The distance formula on `M` immediately gives the normalized
distance law. It also gives a Lipschitz bound with constant `D`, hence
continuity. The defining endpoint distances give `c 0 = x` and `c 1 = y`.
These data form the required Mathlib path. The theorem
`isGeodesicSpace_of_complete_npc` packages this construction, and
`completeNPCGeodesic` proves the exact universe-polymorphic target.

## Scope

This proof supplies the geodesic-existence bridge for complete primitive KP NPC
metric spaces. It introduces no axiom and changes no published target or
definition. It does not prove the bounded-action fixed-point theorem, the
aggregate metric theorem, nearest-point results, or any building construction.
