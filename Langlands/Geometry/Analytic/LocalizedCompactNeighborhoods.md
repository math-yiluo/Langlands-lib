# Stable compact neighborhoods on actual localized analytic spaces

This internal geometric prerequisite works with the existing actual atlas and
localized-space functor, with independent field, space, chart-index and group
universes. It does not assert étale compact acyclicity.

Compact chart images and the actual quasinet neighborhood axiom supply weak
local compactness; Hausdorffness gives local compactness. Saturation and rational
neighborhoods refine each finite quasinet witness to a finite family of original
charts inside a prescribed neighborhood. This adapts the implemented finite
recognized-neighborhood argument in `FullRecognitionEtaleMorphisms`, using
`HasAllLocalDomains.exists_chart` to retain original chart indices.

The actual localized-space action evaluates the existing space functor on the
given analytic automorphisms. Each of its maps is continuous. A continuity test
on a chart with the zero function and bound one implies that a neighborhood of
the group identity preserves that chart. Its full setwise stabilizer is therefore
an open subgroup. Intersecting the stabilizers of finitely many charts makes
their union stable; its interior is an open stable neighborhood. This proves the
existing `HasStableNeighbourhoods` predicate for the actual underlying space,
without a nonarchimedean-group hypothesis.

For a Hausdorff actual space, every compact subset inside an open set has an
open neighborhood whose closure is compact and lies inside that open set, and
which is stable under an open subgroup. First choose a relatively compact open
neighborhood by local compactness. Cover the compact subset by stable open
neighborhoods inside it and take a finite subcover. Their union is stable under
the finite intersection of their open stabilizing subgroups, and its closure
lies in the chosen compact closure. This is the geometric argument of
`CompactSoft.FamilyCutoff.exists_compact_stable_neighbourhood`, specialized
directly to the actual analytic space to retain independent universe levels.

The argument uses only existing Library and Mathlib constructions and their
proved properties; it introduces no original-literature translation. Compact
support and analytic étale derived vanishing remain further obligations.
