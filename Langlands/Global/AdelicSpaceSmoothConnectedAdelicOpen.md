# Smooth connected maps on full model adelic points

This derived unit proves openness on full model adelic points, conditional on
the exact `SpaceUniformLangWeilStatement`. The coefficient ring is an arbitrary
ring of S-integers of a global field; S is nonempty in the function-field
case. Both algebraic spaces are separated and finite type, and their map is
smooth with nonempty geometrically connected fibres. Relative dimension may
vary. No finite-type hypothesis over the integers is imposed on the original
ring of S-integers.

For each stage T above S, `curvePlaceSpacePrincipalStage` and
`numberFieldSpacePrincipalStage` choose the published principal level above T
and regard it as a stage above S. Its actual S-integer ring is finite type over
the integers, so the canonical algebra structure over the lifted integers has
a locally finite-type spectrum map. Base change preserves the separated,
finite-type spaces, smoothness and nonempty geometric connectedness.
`AdelicSpaceSmoothConnectedModelOpen` therefore proves openness on this level.
The stage homeomorphisms and their naturality in the model map transport
openness to the original-S stage point sets.

These selected stages cover the original full adelic points: first use the
published covering by arbitrary stages, then change the point's coefficient
ring from T to the chosen principal stage. Compatibility of stage maps with
transition maps preserves the original adelic point.

The general helper `isOpenMap_of_continuous_cover` uses a continuous surjection
from the disjoint union of the covering source stages. Each restriction of
the composite with the global map is open, since its stage map and its target
inclusion are open. Openness descends along the continuous surjection. The
published adelic topology theorem supplies continuous source inclusions and
open target inclusions, as each stage inclusion is an open embedding.
This proves `curvePlaceSmoothConnectedAdele_isOpenMap` and
`numberFieldSmoothConnectedAdele_isOpenMap`.

Every infinite number-field coordinate is retained by the actual levels,
their transitions and the full adelic point topology. The provenance is
internal to the published level topology, cofinal principal rings, base-change
properties and the smooth connected level-openness construction. The exact
Lang–Weil premise remains explicit. This unit neither proves that estimate
nor claims the unconditional `AdelicSpaceSpreadSmoothOpenStatement`.
