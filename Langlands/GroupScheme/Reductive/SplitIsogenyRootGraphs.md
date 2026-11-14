# Source root subgroups in graphs of local isogenies

This is derived supporting work for the split isogeny theorem. It adapts the
source-side root-lift argument in `SplitLeviGluingRootGraphs` to
`LocalIsogenyGraphEnvelope`, whose local maps may be inseparable and whose
source and target tori may differ. No root transport to the target is assumed.

`LocalIsogeny.SourceRoot` stores an actual smooth connected closed representative
of a nonzero source root functor in one source centralizer. `sourceRoot`
constructs it from the published intrinsic-root representability theorem.
When the root annihilates the centralizer direction, `ambientRep` uses
`LeviGluing.root_map_centralizer` to show that its composite into the source
group represents the entire ambient source root functor, on every scheme test.

The graph lift is its inclusion followed by the local graph lift. Its first
projection is the ambient source root inclusion; its second projection is the
actual local isogeny followed by the target centralizer inclusion. Closedness
follows by composition of closed subgroup inclusions.

The intrinsic source-torus action on the local root representative intertwines
with conjugation by the graph torus, since the local source torus lifts to that
graph torus. This proves normalization on every scheme test. Functoriality of
the intrinsic root functor then puts the lifted subgroup in the graph root
functor for the same source character.

These statements retain the actual local isogenies. They assert no
representability or isomorphism property for the second root projection, and
do not prove maximality of the graph torus or general isogeny realization.
