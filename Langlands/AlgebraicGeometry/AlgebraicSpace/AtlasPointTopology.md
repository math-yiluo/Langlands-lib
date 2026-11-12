# The quotient topology from an étale atlas

Author: Worker 107.

This internal construction defines `chartPointMap a : U.left → Points F` for a scheme
chart `a : h_U ⟶ F`. No sheaf or finiteness assumption on `F` is required.

`surjective_chartPointMap` shows that a geometrically surjective representable chart is
surjective on quotient points. Pull the chart back along a field-valued section, choose a
point above the unique point of its field spectrum, and use the represented pullback
square to compare the two resulting quotient points.

For an étale surjective chart, `isOpen_pointTopology_iff_atlas` states that a subset of
`Points F` is open precisely when its inverse image in `U.left` is open. For each other
étale chart, pull back the supplied atlas. The projection onto that other chart is an
étale surjective morphism of schemes, hence an open quotient map, so openness descends
from the pullback. `isQuotientMap_chartPointMap` combines this open-set test with point
surjectivity.

These are consequences of the existing point quotient and étale-chart topology and
Mathlib's scheme pullback and étale openness results. They are prerequisites for the
component comparison in Conrad's Lemma 5.1, not a constructibility proof.
