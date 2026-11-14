# Affine Cartan extensions on actual absolute Tits-index vertices

`titsIndexCartanExtension` chooses an integer matrix on `Option d.Vertex`
extending the exact absolute Cartan matrix of supplied actual Tits-index
data `d` of a group `G` over a field `k`. The extension `L/k` must embed
compatibly into `SeparableClosure k`. A split maximal torus of `G_L` is
supplied. The apartment is an affine torsor over the actual reduced real
cocharacter space of that torus, and the entire derivative set of the
supplied affine root system must equal the range of actual root forms.

The affine assumptions are a regular chamber point, nonempty irreducible
roots, vertex transitivity of the chamber Cartan matrix, indivisible lifts
for every full derivative root, and root-preserving affine pullbacks
acting transitively on the simple affine roots. None of these hypotheses
is discharged by this construction.

`titsIndexCartanExtension_spec` proves that the chosen matrix has diagonal
two, nonpositive off-diagonal entries, a symmetric zero pattern, a strictly
positive integral left-kernel vector, and a transitive action of its
entry-preserving permutations. Its block on `some` is literally `d.cartan`.
The supporting theorem `exists_transitive_titsIndexCartanExtension` proves
existence before classical choice defines the matrix.

The proof uses published actual root-datum existence to obtain a finite
reduced integral datum on the supplied split maximal torus. Semisimplicity
from `d` gives connected reductivity after field extension. The full
root-datum comparison with `d.pinning` transports its specific simple
base to this datum. The imported actual integral-to-derivative Cartan
extension then gives a matrix on `Option` of that base's support. The
actual Tits-index vertex equivalence, extended by `Option`, reindexes the
matrix, its positive left-kernel vector and its transitive permutations.
The exact integer Cartan identity for the transported base identifies the
resulting principal block with `d.cartan`.

This is an internal composition of the imported constructions. It proves
no existence theorem for a split maximal torus, actual affine building,
regular chamber, irreducibility, lifts or transitivity. In particular,
`LocalAnisotropicAffineDiagramStatement` remains unproved until these
inputs are constructed for every anisotropic absolutely almost-simple
local group without added assumptions. The present construction is over
arbitrary fields and has no field-characteristic restriction.
