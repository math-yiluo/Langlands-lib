# Kaletha–Prasad metric fixed-point statements

This module states the metric foundation needed by Bundle A of the KP
Bruhat–Tits program. It imports the published
`Langlands.Geometry.Metric.KPDefinitions` interface. Every declaration here is a
definition returning `Prop`; no theorem in this module supplies a proof of any
of these targets.

The namespace is `Langlands.Geometry.Metric.KP`. The carrier of a metric space
has universe `uX`, and the carrier of an acting group has an independent
universe `uG`. Each component universally quantifies the metric spaces and
structures it uses. `MetricFixedPointFoundationStatement` is the conjunction of
all six components, with these universe parameters retained.

## Sources

The normative sources are:

- `kaletha-prasad-2023-bruhat-tits-new-approach`, Kaletha and Prasad,
  *Bruhat–Tits Theory: A New Approach* (2023), Section 1.1, printed pp. 4–7,
  PDF pp. 35–38. SHA-256:
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- `kaletha-prasad-2024-corrections`, *Corrections and additions in the book
  “Bruhat-Tits theory: a new approach”*, version of 1 November 2024,
  Section 1.1, PDF pp. 1–2. SHA-256:
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

Both registered PDFs are in
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/`.
The source locators below refer to those copies.

## Statement correspondence

| Declaration | Source | Exact content |
| --- | --- | --- |
| `GeodesicUniquenessStatement` | Lemma 1.1.11, printed p. 5 / PDF p. 36 | In an NPC geodesic space, each ordered endpoint pair has exactly one normalized geodesic. For every such geodesic, a point satisfies the NPC inequality for its endpoints if and only if it is the value at parameter `1/2`. |
| `ClosedBallConvexityStatement` | Lemma 1.1.13, printed pp. 5–6 / PDF pp. 36–37, corrected at corrections PDF p. 1 | Every closed ball with nonnegative real radius in an NPC geodesic space is convex in the corrected nonempty sense. |
| `ClosedConvexHullStatement` | Definition 1.1.14 and the paragraph after it, printed p. 6 / PDF p. 37; corrections PDF p. 1 | For nonempty bounded `M` in an NPC geodesic space, the specified intersection is a closed, bounded, convex superset of `M`. |
| `BarycenterStatement` | Theorem 1.1.15(1), printed pp. 6–7 / PDF pp. 37–38; proof corrections at corrections PDF p. 2 | In a complete NPC geodesic space, a nonempty bounded closed convex set has a unique barycenter, and every barycenter is fixed by all isometries mapping the set onto itself. |
| `BoundedSetStabilizerFixedPointStatement` | Theorem 1.1.15(2), printed p. 6 / PDF p. 37 | In a complete NPC geodesic space, all isometries preserving an arbitrary nonempty bounded subset have one common fixed point in the ambient space. |
| `BoundedActionFixedPointStatement` | Corollary 1.1.19, printed p. 7 / PDF p. 38, with Lemma 1.1.17 and Definition 1.1.18 on that page | An isometric group action on a nonempty complete NPC metric space with a bounded orbit has a fixed point. No geodesic hypothesis is added to the printed corollary. |
| `MetricFixedPointFoundationStatement` | The preceding six source items | A conjunction recording this coherent interface, with no additional mathematical conclusion. |

The primitive NPC condition is exactly Definition 1.1.8: for any `x,y` there
exists `m` such that, for every `z`,

`2 d(m,z)^2 + (1/2) d(x,y)^2 ≤ d(x,z)^2 + d(y,z)^2`.

It contains no completeness, geodesic, convexity, barycenter or fixed-point
conclusion. The imported module already proves its normalized geodesic
definition equivalent to the literal curve-length Definition 1.1.2. The
uniqueness statement therefore concerns the source's parameterized geodesics,
including constant geodesics between coincident endpoints.

The midpoint clause is an equivalence for every candidate point, rather than
an existence claim for some midpoint. Together with unique geodesic existence,
it states exactly the two conclusions of Lemma 1.1.11. No completeness
assumption is needed for this lemma or for the closed-ball and hull statements.

The correction on PDF p. 1 changes “metric space” to “geodesic space” in
Lemma 1.1.13 and the item called “Remark 1.1.14”. The book's item 1.1.14 is a
definition; the hull target follows that definition and the immediately
following paragraph, with the corrected ambient hypothesis. The explicit
condition `0 ≤ r` on a closed ball records the admissible geometric radii:
a negative-radius Mathlib closed ball is empty and cannot satisfy the
corrected nonempty convexity predicate. Radius zero is retained.

`IsGeodesicallyConvex M` includes `M.Nonempty`, as required by the correction
to Definition 1.1.12(1). The barycenter target uses this nonemptiness and
separately assumes boundedness and closedness. The imported `IsBarycenter`
requires membership in `M` and attainment of the infimum over centers *in*
`M`; its extended nonnegative radius is finite for the sets used here.
Uniqueness is stated for all barycenters, separately from the invariance
clause. It is not merely uniqueness among invariant barycenters.

In both parts of Theorem 1.1.15, preservation means `e '' M = M` for a
surjective isometry `e : X ≃ᵢ X`. The common fixed point in part (2) is
quantified before all preserving isometries. It is not a choice of a
different fixed point for each isometry, and need not belong to the original
bounded set. The set in part (2) is not required to be closed or convex.

The action formulation of Corollary 1.1.19 uses Mathlib `MulAction`,
`IsIsometricSMul` and `MulAction.fixedPoints`, and the imported
`HasBoundedAction X (Set.univ : Set G)`. An action of a group by isometries
gives bijective isometries because inverse group elements act as inverse
maps. It therefore factors through a subgroup of the isometry group; no
faithfulness hypothesis is needed. Conversely every subgroup of that
isometry group has its evaluation action, supplied by the imported scoped
instances. This explains the source-equivalent formulation by arbitrary
groups. It imposes no topology, compactness or finiteness assumption on the
group. The bounded orbit and fixed-point conclusions use the actual action.

The printed Corollary 1.1.19 does not assume geodesic existence. A later proof
that invokes Theorem 1.1.15 must discharge that missing hypothesis, for
example by constructing geodesics from completeness and the primitive NPC
midpoints. That construction remains a proof obligation. The statement does
not assume it, nor does it assume a barycenter or a fixed point.

## Proof and release boundaries

The corrections to the proof of Theorem 1.1.15 restrict a positive error to
`ε < r` and allow the approximating errors to be nonnegative. A later proof
must also handle radius zero and approximants attaining the infimum; the
statements here impose neither `r > 0` nor failure of attainment. No numerical
estimate from that proof is made an assumption.

Proposition 1.1.20 concerns nearest-point projections and is outside this
focused statement unit. Its corrected printed intermediate estimate and its
zero-distance continuity argument have separate repair obligations recorded
in the parent program's private source audit. None of those numerical
estimates is asserted or used here.

This module introduces no axioms and proves no major KP result. Its
publication supplies statement targets for later independent proofs.
Constructing a Bruhat–Tits building, proving its completeness and NPC and
geodesic hypotheses, verifying corrected Theorem 9.2.7, and closing Bundle A
or any release remain separate obligations of the parent program. No
external Lean code is used.
