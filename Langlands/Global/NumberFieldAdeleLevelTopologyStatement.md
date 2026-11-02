# Topology of actual full number-field adelic levels

Author: Worker 208.

`NumberFieldAdeleLevelTopologyStatement` asserts four properties for every
number field in an arbitrary common universe `u`:

1. The existing `numberFieldAdeleLevelProductEquiv` is a homeomorphism from
   the actual level subring, with its topology induced from `Adeles K`, to
   the product of all archimedean completions, the finite completions at
   the selected finite places, and the completed valuation rings at the
   other finite places. All factor and product topologies are the existing
   ones; the topology is not transported along this ring equivalence.
2. Each literal inclusion `numberFieldAdeleLevelMap` for `S ⊆ T` is an open
   embedding for those subspace topologies.
3. Every element of the existing full adele ring belongs to a finite level.
4. For a map to any topological space in `u`, continuity is equivalent to
   continuity on each level. This is the final topology of the level cover.

The finite part `S` may be empty. The corresponding all-place set is
`numberFieldLevelPlaces K S`, which includes every archimedean place and
is already proved nonempty in the construction. Thus the statement uses
Conrad's nonempty all-place convention.

This is derived arithmetic infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.1,
the open-level description of the adelic topology, and printed pp.6–8,
Theorem 3.6 and the local factors in (3.6.1). Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The target specializes this arithmetic description to the existing
number-field adele ring and its existing canonical coordinate equivalence.

This statement does not itself provide a proof. A categorical colimit
universal property, global function fields and their omitted places,
presentation independence, model descent, and scheme or algebraic-space
point comparisons remain separate obligations of the whole-paper program.
