# Barycenters in complete NPC geodesic spaces

This proof unit establishes `Langlands.Geometry.Metric.KP.BarycenterStatement`
from `KPFixedPointStatement`, with arbitrary carrier universe and exactly its
published hypotheses. The theorem is `Langlands.Geometry.Metric.KP.barycenter`.

The normative source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
Theorem 1.1.15(1), printed pp.6–7 / PDF pp.37–38, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, PDF pp.1–2, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
require nonempty convexity and repair the approximating errors in the printed
proof. Both source passages were read. Their registered copies are under
`/home/taskhub/central-library/Kaletha-Prasad--Bruhat-Tits theory, a new approach (book)--2023/`.

The implemented argument follows the source's minimizing-sequence strategy,
using an independently derived squared estimate that also treats radius zero
and attained minima. Put `f(x) = (jointDiam {x} M).toReal` and
`r = (radius M).toReal`. The intrinsic boundedness lemmas identify these as
actual finite suprema and an infimum. Taking a sequence of distances converging
to `f(m)` in the primitive NPC inequality gives

`2 f(m)^2 + d(x,y)^2 / 2 ≤ f(x)^2 + f(y)^2`.

The published geodesic-midpoint theorem identifies a geodesic midpoint with an
NPC midpoint. Convexity puts it in `M`, so `r ≤ f(m)` and nonnegativity give

`d(x,y)^2 ≤ 2 f(x)^2 + 2 f(y)^2 - 4 r^2`.

Mathlib's GLB approximation lemma supplies a sequence of values of `f` tending
to `r`, including a constant sequence when the infimum is attained. Choose
centers realizing those values. The displayed estimate makes the sequence
Cauchy. Completeness supplies its limit, and closedness keeps it in `M`.
Passing each distance bound to the limit shows its joint diameter is at most
`r`; the infimum bound supplies the reverse inequality. The same squared
estimate gives distance zero between any two barycenters.

Finally simultaneous isometric transport preserves joint diameter. A
set-preserving surjective isometry therefore sends a barycenter to another
barycenter of the same set, and uniqueness proves that it fixes the point.
No local compactness, dimension bound, properness, positive radius or
non-attainment assumption is used. The auxiliary estimates and transport
lemmas are derived here; no external Lean code is adopted.
