# Bounded charts of actual projective point spaces

Author: Worker 105.

This internal prerequisite uses the Library's actual polynomial projective
scheme, its degree-zero homogeneous localization chart rings and its actual
relative scheme-point carrier. It is motivated by the projective case in
Conrad, *Weil and Grothendieck approaches to adelic points*, December 31, 2011,
Proposition 4.4, printed page 11, registered source
`conrad-2011-weil-grothendieck-adelic-points`. The compactness theorem remains a
separate statement and proof obligation.

`relativeChartInclusion` is the existing projective chart inclusion, equipped
with its actual equation over Spec K. `relativeChartPoint` postcomposes the
spectrum of an actual chart algebra map with this inclusion. Forgetting the
base equation gives exactly the existing `chartPoint`.

For every field topology with continuous multiplication and open units in the
precise sense of `IsOpenUnits`, this map is continuous from the chart's
algebra-map evaluation topology to `schemePointTopology` on the actual relative
projective points. The proof uses the actual spectrum/algebra-point
homeomorphism and continuity of postcomposition from an affine source.

For every normed field K, `boundedChart K n j` consists of actual chart algebra
points on which each ratio X_k/X_j has norm at most one.
`boundedChartImage K n j` is its image in the actual relative projective point
space. These definitions apply to every natural dimension n and each of the
n+1 chart indices, without assumptions on characteristic or on local compactness.

`exists_mem_boundedChartImage` proves that these finitely many images cover
all actual relative projective points. Starting with the existing normalized
coordinates of a point, it chooses an index with maximal norm. The previously
normalized coordinate has value one, so the maximal coordinate is nonzero.
Evaluating the selected chart at this vector gives ratios of norm at most
one; the published rechart comparison identifies the resulting scheme morphism
with the original point. Equality in the slice category then gives equality
of relative points. `iUnion_boundedChartImage` expresses this cover as equality
with the entire point carrier. These results use only a normed field, and do
not assert compactness for discrete trivially normed fields.
