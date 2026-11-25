# Gluing equality of group-scheme homomorphisms over open subsets

This module is internal, derived group-scheme infrastructure. It uses the
published actual pullback comparisons in `Descent.Data` and fppf locality of
homomorphism equality in `FppfHomLocality`. Its results do not require finite
type, flatness, separatedness, or commutativity assumptions on the groups.

`iterated_baseChange_eq_iff` identifies equality after an iterated pullback with
equality after the direct pullback. It uses naturality of the canonical
isomorphisms for both the source and target group schemes and cancels their
invertible morphisms. `baseChange_eq_of_factor` follows by functoriality.
`fibre_eq_of_open_eq` factors the residue-field morphism through an open
containing the base point and applies that persistence result.

`eq_on_open_of_locally_eq` glues equality on open neighborhoods covering an
open subset `U` of the base. At each point of `U`, it pulls a given neighborhood
back to `U`, transports its equality through the direct/iterated comparison,
and applies the published locality theorem for pointwise etale neighborhoods.
All the neighborhoods used here are open immersions.

`isOpen_fibre_eq_set` and `openLocus` assume that equality
on a residue-field fibre extends to an open neighborhood of that point.
The theorem proves openness using the supplied local extension and
persistence to other fibres. The definition constructs the actual open subset
with that underlying set; `mem_openLocus_iff` gives its precise membership
criterion. `exists_open_fibre_eq_locus` uses this constructed open and glues the
supplied local equalities to show that the homomorphisms agree over it.

These are conditional locality results. They supply neither the local
extension hypothesis nor closedness of the fibre equality set.
