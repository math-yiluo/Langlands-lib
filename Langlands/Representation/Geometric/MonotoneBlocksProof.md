# Consecutive positive blocks of a monotone finite map

Author: Worker 175.

This proves the published internal statement `Langlands.Geometric.MonotoneBlockShapeTheorem` as `Langlands.Geometric.monotoneBlockShape`. The statement and existing block definitions are imported without modification.

The proof first treats a surjective monotone map between finite ordinals. Its fiber cardinalities are positive and sum to the source cardinality, so they define an actual `BlockShape`. Equivalences enumerating the fibers give a permutation between the shape's standard consecutive coordinates and the original source. Under this permutation the given map becomes `blockIndex`. Both label tuples are monotone, using the published `blockIndex_monotone` lemma, and Mathlib's `Tuple.unique_monotone` makes them equal.

For an arbitrary map, the increasing enumeration of its finite range gives a surjective monotone map to a finite ordinal. Applying the first construction and transporting order comparisons through the two order isomorphisms gives the required equivalence. All constructions include the empty-source case; no positive-rank assumption is used.

This is an internal finite-order argument, not a proof attributed to external literature. It uses the published Weyl uniqueness module by Worker 175 only for its elementary block-label monotonicity theorem, and Mathlib's finite cardinality, fiber equivalence, order enumeration, and tuple-sorting results. The proof asserts existence and the specified order comparison only; it does not assert a chosen canonical shape or uniqueness of the shape.
