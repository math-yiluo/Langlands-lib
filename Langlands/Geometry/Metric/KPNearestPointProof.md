# Nearest-point projection in complete NPC geodesic spaces

`Langlands.Geometry.Metric.KP.nearestPointProjection` proves the exact published
`Langlands.Geometry.Metric.KP.NearestPointProjectionStatement` from
`KPNearestPointStatement`, with arbitrary carrier universe `uX`. It constructs
one function `π : X → Y`, proves its minimality and uniqueness, and proves
continuity and equivariance under every ambient isometry equivalence preserving
`Y` setwise. The same projection precedes the quantifier over isometries.

The assumptions are precisely the metric structure, completeness, the primitive
KP NPC condition, geodesic existence, and closed nonempty geodesic convexity of
`Y`. Nonemptiness is part of the published convexity predicate. The set may be
unbounded, the minimum distance may be zero, and the distance infimum may already
be attained. There is no supplied minimizer or supplied projection.

## Sources and provenance

The normative originals are Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
Proposition 1.1.20(1)–(3), printed pp.7–8 / PDF pp.38–39, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`;
and the authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, Section 1.1, PDF pp.1–2, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
Both passages were read. Their registered PDF copies are under
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/`.

The construction follows the source's minimizing-sequence strategy, with an
independently derived squared estimate replacing the incorrect coefficient-2
estimate printed in the corrections. The continuity argument also avoids the
corrections' multiplicative error relative to a possibly zero minimum distance.
These are proof repairs, not additional premises or changes to the target.
The helpers in this module are derived results. The published
`KPGeodesicUniquenessProof` supplies the geodesic midpoint's NPC inequality;
no external Lean code is adopted.

## Implemented proof

`dist_sq_le_nearest_deficit` starts with any nonnegative lower bound `r` for
the distances from `x` to points of `Y`. A geodesic midpoint `m` of `y,z ∈ Y`
lies in `Y` by convexity. The primitive NPC inequality and `r ≤ d(x,m)` give

`d(y,z)^2 ≤ 2 d(x,y)^2 + 2 d(x,z)^2 - 4 r^2`.

This is the formal estimate used throughout. In particular, approximating
distances less than `r+δ` would give the sufficient coefficient-4 bound
`d(y,z)^2 < 4δ(2r+δ)`. The proof uses the squared distances directly.

`exists_nearestPoint` takes the real infimum of `D = {d(x,y) | y ∈ Y}`.
Nonemptiness of `Y` makes `D` nonempty, and zero is a lower bound; upper
boundedness is unnecessary. Mathlib's `IsGLB.exists_seq_antitone_tendsto`
provides values in `D` tending to the infimum, including attained infima.
Choose points realizing these values. Once their squared distances to `x`
are less than `r^2+ε^2/4`, the deficit estimate makes their mutual distance
less than `ε`. Thus the chosen sequence is Cauchy. Completeness gives its
limit, closedness puts it in `Y`, and continuity of distance identifies its
distance to `x` with the infimum.

`nearestPoint_unique` applies the same deficit with `r` equal to the distance
of a minimizing point. Any other point at that distance has squared separation
at most zero, so the points, and hence their subtype elements, are equal.

`continuous_of_nearestPoint` proves continuity for any function satisfying
minimality. Fix `x`, put `r=d(x,π(x))` and `q(z)=d(x,π(z))`, and use

`r ≤ q(z) ≤ d(x,z)+d(z,π(x))`.

The outer expressions tend to `r` as `z` tends to `x`, so the squeeze theorem
gives `q(z) → r`. The midpoint deficit specializes to

`d(π(z),π(x))^2 ≤ 2 q(z)^2 - 2 r^2`.

The right side tends to zero. An eventual bound by `ε^2` gives the metric
continuity criterion directly in the inherited subtype metric. The argument
uses neighborhood filters rather than sequences and never divides by `r`.

`nearestPoint_isometry` compares `π(e(x))` with `e(π(x))`. Setwise preservation
puts the latter in `Y` and supplies a preimage in `Y` of the former. Minimality
at `e(x)` gives one distance inequality; minimality at `x` and distance
preservation give the reverse. Uniqueness identifies the points. Finally,
`nearestPointProjection` chooses minimizers for all `x` once and applies these
three properties to that same choice.
