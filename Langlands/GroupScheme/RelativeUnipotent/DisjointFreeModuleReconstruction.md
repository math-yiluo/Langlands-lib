# Sheaf-map reconstruction on disjoint free presentations

This internal Task 7200 construction uses an actual disjoint open cover with an
actual finite free isomorphism for the source module on each piece. The piece
ranks may differ, and the target module is arbitrary.

The original natural section transformation is restricted using the canonical
pullback-composition comparisons. Free-source reconstruction gives each local
module morphism. Disjoint-cover morphism gluing then constructs an actual
global module morphism, retaining the prescribed original maps on every piece.
The same presentations pull back along arbitrary scheme maps. All-test section
actions detect actual module morphisms, by the original free generators on
each piece.

`reconstruct_apply` proves recovery on all sections of every scheme test.
Its proof uses the actual disjoint inverse-image cover of that test,
canonical section-composition comparisons and the original transformation's
naturality. `reconstruct_unique` gives uniqueness among actual module maps
with that action. Natural inverse transformations construct an actual module
isomorphism with the reconstructed original maps in both directions.

The provenance is derived from canonical pullback coherence, actual free-source
reconstruction and actual disjoint-cover morphism gluing. This is infrastructure
for the supplied-radical quotient overlap cocycle.
