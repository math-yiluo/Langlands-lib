# Metrics glued from apartments along distance-nonincreasing retractions

This module isolates the metric part of Kaletha–Prasad (2023), Section 4.2: the
proof of Proposition 4.2.3(1), that the building distance is a metric, and of
Proposition 4.2.7, that the building is nonpositively curved. The proofs there
only use three properties of the building, its apartments and the retractions
`ρ_{A,C}`. The predicate `KP.IsRetractionGluedDistance d 𝒜` records exactly
these properties for a function `d : X → X → ℝ` and a family `𝒜` of subsets of
an arbitrary type `X`:

* `exists_common`: any two points of `X` lie in a common member of `𝒜`
  (in the source this follows from the building axioms; compare
  Proposition 1.5.14, used in the same way in the proof of Lemma 4.2.11);
* `apartment`: on each member `A` of `𝒜` there is a metric whose distance is
  the restriction of `d`, and `A` is nonpositively curved for it, in the sense
  of the Library predicate `KP.IsNonpositivelyCurved` (KP Definition 1.1.8);
* `exists_retraction`: for every `A ∈ 𝒜` and every `m ∈ A` there is a map
  `ρ : X → X` with values in `A`, equal to the identity on `A`, which does not
  increase `d` and preserves the `d`-distance from `m`.

The last clause abstracts KP Lemma 4.2.2: for a chamber `C` of `A` whose
closure contains `m`, the retraction `ρ_{A,C}` does not increase distances
(4.2.2(3)) and preserves the distance from `m` (4.2.2(2), first case). Only the
point `m` is recorded, not the chamber; this is the derived part of the
predicate.

Results:

* `dist_self`, `comm`, `nonneg`, `eq_of_eq_zero`: the metric axioms other than
  the triangle inequality, read off in a common apartment;
* `triangle`: KP Proposition 4.2.3(1). For `x, z` choose a common apartment `A`
  and a retraction onto `A` centred at `x`; then
  `d x z = d (ρ x) (ρ z) ≤ d (ρ x) (ρ y) + d (ρ y) (ρ z) ≤ d x y + d y z`;
* `metricSpace`: the `MetricSpace X` with distance `d`
  (`dist_metricSpace` is the defining equation);
* `isNonpositivelyCurved`: KP Proposition 4.2.7. For `x, y` take a common
  apartment `A`, the NPC midpoint `m` of `x, y` in `A` and a retraction centred
  at `m`. The NPC inequality in `A` at `ρ z`, together with
  `d m (ρ z) = d m z`, `d x (ρ z) ≤ d x z` and `d y (ρ z) ≤ d y z`, gives the
  inequality at `z`. In the source `m` is the Euclidean midpoint and the
  parallelogram law is an equality; the Library predicate only requires the
  inequality, which is what is used;
* `exists_apartmentMetric_of_injective`: the image of an injective map
  `e : P → X` from an NPC metric space, along which `d` pulls back to the
  metric of `P`, satisfies the `apartment` clause. This is how apartments
  given as images of a model apartment are fed into the predicate.

The predicate is a derived abstraction: Kaletha–Prasad state these results for
the building `B(G)` only. Sources: Kaletha–Prasad (2023), Lemma 4.2.2,
Proposition 4.2.3(1) and Proposition 4.2.7, printed pp.169–170 /
PDF pp.200–201, read with the corrections of 1 November 2024, Section 4.2,
PDF pp.28–29. Nothing about a building, a group action or completeness is
proved here.

The candidate also contains three helper modules, each with its own Markdown:
`Langlands.Geometry.Building.FacetClosureLipschitz` (the segment subdivision
in the proof of Lemma 4.2.2(3)),
`Langlands.Geometry.Building.AffineRootOrbitDiscreteness` (the apartment step
of Lemma 4.2.11) and `Langlands.Geometry.Metric.DiscreteOrbitCompleteness`
(Theorem 4.2.10 in abstract form).

Author: Worker 1221.
