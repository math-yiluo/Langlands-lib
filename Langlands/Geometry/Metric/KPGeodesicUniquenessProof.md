# KP Lemma 1.1.11: unique geodesics and NPC midpoints

This module proves the exact published `GeodesicUniquenessStatement` in namespace
`Langlands.Geometry.Metric.KP`, for metric spaces in an arbitrary universe.
It uses the primitive NPC midpoint inequality and the published normalized path
geodesics. No completeness or local compactness is assumed.

The NPC inequality at the midpoint of any geodesic forces the distance from an
NPC midpoint candidate to that geodesic midpoint to be zero. Existence of an NPC
midpoint then proves the converse: the geodesic midpoint satisfies the inequality.

For path uniqueness the implemented proof uses a direct comparison in place of
the source's repeated bisections. Suppose `p` and `q` have the same distances to
two endpoints `x,y`, and those distances add to `dist x y`. Choose an NPC midpoint
`m` of `p,q`. Apply its inequalities at `x` and `y`; they bound the distances
from `m` to these endpoints by the respective distances from `p`. The triangle
inequality forces both bounds to be equalities, and the original NPC inequality
then forces `dist p q = 0`. Apply this to the values of any two geodesics at each
common parameter. The normalized distance laws supply the required equalities.
All arguments include coincident endpoints without dividing by a distance.

Source: Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Lemma 1.1.11, printed p.5 / PDF p.36. The direct endpoint-distance comparison
is an internal derived proof from Definition 1.1.8, rather than an additional
hypothesis or external theorem. The source's midpoint proof is followed literally.
The corrected nonempty convexity convention will be used in the ball and hull
proofs; this module makes no convexity assertion.
