# Topology of arithmetic coefficient changes over a fixed model base

`AdelicFixedModelTransitionTopologyStatement` states the continuity and openness
of the literal coefficient maps in the two arithmetic fixed-model point
diagrams. For an initial finite set `S`, a finite-type model `X` over its
outside-`S` integer ring, and finite superlevels `T ⊆ U`, the map is
`RingPoint.changeRing` for `curvePlaceAdeleLevelOverMap` or
`numberFieldAdeleLevelOverMap`. Both its source and target are actual points
of the same original model `X`, with the original initial scalar action.

The topologies are `curvePlaceFixedModelStageTopology` and
`numberFieldFixedModelStageTopology`. These transport the arithmetic topologies
of the actual models pulled back to `T` and `U` through the canonical point
equivalences. Each coefficient map is asserted to be continuous and open.
If the original model is separated, it is asserted to be an open embedding.
Finite type is expressed as local finite type and quasi-compactness. The
continuity and openness assertions impose no separatedness or affineness.

This is a derived reformulation of Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), Theorem 3.6, printed p.6, with its
transition argument on p.8, in the fixed-model presentation of (3.5.1).
The canonical iterated-to-direct model pullback isomorphism from
`AdelicFixedModelTransition` identifies the original changing-model transition
with the literal fixed-base coefficient map. Thus the two model presentations
are compared by actual isomorphisms; their pullback objects are not identified
by definitional equality.

The curve clause retains arbitrary constant fields and the compatible
rational-function presentation and scalar tower required for a function field.
The number-field clause uses the full adele levels, retaining all infinite
factors. Both clauses hold in an arbitrary common universe, allow an empty
initial finite set, and apply to arbitrary nonaffine finite-type models.
This target does not assert model independence, generic-fiber identification,
or openness of the maps into the adelic point colimit.
