# Kaletha–Prasad nearest-point projection statement

`Langlands.Geometry.Metric.KP.NearestPointProjectionStatement` states all three
parts of KP Proposition 1.1.20. It is a universe-polymorphic definition returning
`Prop`. This module supplies a target for a later proof; it neither constructs
a projection nor proves its existence.

The imported `Langlands.Geometry.Metric.KPDefinitions` supplies the primitive NPC
midpoint inequality, normalized geodesics and the corrected nonempty convexity
predicate. No new geometric objects or predicates are introduced here.

## Sources and correspondence

The registered originals are:

- `kaletha-prasad-2023-bruhat-tits-new-approach`, Kaletha and Prasad,
  *Bruhat–Tits Theory: A New Approach* (2023), Proposition 1.1.20,
  printed pp. 7–8 / PDF pp. 38–39. SHA-256:
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- `kaletha-prasad-2024-corrections`, *Corrections and additions in the book
  “Bruhat-Tits theory: a new approach”*, version of 1 November 2024,
  Section 1.1, PDF pp. 1–2. SHA-256:
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

Both PDFs are in
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/`,
with filenames `Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023.pdf`
and `Kaletha-Prasad--Corrections and additions to Bruhat-Tits theory, a new approach--2024.pdf`.

The metric-space carrier has arbitrary universe `uX`. The assumptions are
completeness, the primitive NPC condition, geodesic existence, and a closed
geodesically convex subset `Y`. Convexity includes nonemptiness by corrected
Definition 1.1.12(1). There is no boundedness, properness, finite-dimensionality,
local compactness or positive-distance assumption.

The existential function `π : X → Y` selects a point of the actual subtype
`Y` for each ambient point. Its first clause says that its distance to `x` is
minimal among all points of `Y`. The second says that any point at that minimal
distance equals `π x`. Together these clauses express the unique nearest point
of part (1), for every `x`. In particular any other distance-minimizing point
has equal distance by the two minimality inequalities.

`Continuous π` uses the metric topology of `X` and the inherited subtype
topology of `Y`, as in part (2). The final clause is part (3): every isometry
equivalence `e : X ≃ᵢ X` with `e '' Y = Y` commutes with the projection. The
equation is written in `X` after coercing the projected points; it uses the
actual ambient isometry and subset. The same function `π` is chosen before all
preserving isometries.

## Proof boundary and numerical corrections

The 2024 corrections modify the proof of parts (1) and (2), without adding a
positive-distance hypothesis to the proposition. Their displayed intermediate
estimate in part (1), with coefficient `2`, cannot be used as printed. For
example, in the Euclidean plane take `Y` to be the horizontal axis,
`x = (0,1)`, `y₁ = (-1,0)`, `y₂ = (1,0)`, `r = 1` and `ε = 1/2`.
Both distances to `x` equal `√2 < r + ε`, while
`d(y₁,y₂)² = 4 > 2 ε (2r + ε) = 5/2`.
This also has `0 < ε < r`.

An independent midpoint estimate gives

`d(y₁,y₂)² ≤ 2 d(x,y₁)² + 2 d(x,y₂)² - 4r²`,

where `r` is the infimum of distances to `Y`. Indeed the midpoint lies in
`Y`, so its distance to `x` is at least `r`, and the primitive NPC inequality
gives the displayed bound. For approximants with distance less than `r + ε`,
the corresponding valid strict bound has coefficient `4`:
`d(y₁,y₂)² < 4 ε (2r + ε)`. This tends to zero and supplies the Cauchy
minimizing-sequence route to existence; the exact bound also gives uniqueness.
This is a rationale for a later proof, not an implemented theorem here.

The correction's multiplicative error expression for continuity requires
separate treatment when `r = d(x,π x) = 0`. A division-free route retains the
minimality and triangle inequalities from the source, which force
`qₙ = d(x,π xₙ)` to tend to `r`, and uses the midpoint estimate
`d(π xₙ,π x)² ≤ 2(qₙ² - r²)`. This bound includes `r = 0`.
Equivariance follows from distance preservation, preservation of `Y` and
uniqueness, as in the source. These proof obligations remain open.

Neither the faulty printed estimate nor any substitute numerical estimate is
a premise or conclusion of this Lean statement. The target asserts the
proposition's qualitative conclusions with their original hypotheses.
It changes no existing statement or definition, uses no external Lean code,
and closes no building construction, bundle or release.
