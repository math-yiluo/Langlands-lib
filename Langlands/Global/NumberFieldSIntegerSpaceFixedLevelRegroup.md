# Original upper-place regrouping of number-field space Weil stages

This internal construction compares actual enlarged arithmetic stages of
an original S-integer model and its Weil restriction, using the original
upper-place indexing and original point topologies.

Let `L/K` be an extension of number fields, let `S` be a finite set of
finite places of `K`, and let `T` be an enlarged support containing `S`.
The upper initial support is the full preimage of `S`, and `upperLevel`
is the full preimage of `T` viewed above it. `indexEquiv` is the published
bijection from pairs consisting of a lower `T`-coordinate and an upper
place above it to the actual upper-level coordinates.

For an algebraic space `X` over the fixed upper S-integers,
`factorPointHomeomorph` compares the upper local factor point space at
a pair with the same factor regarded as its actual upper-stage coordinate.
Each factor has its original field-valued topology, including the topology
on completed-integer points induced through the original completed field.
Case analysis on infinite, finite-field and finite-integer coordinates
reduces these comparisons to identity homeomorphisms. Their underlying
coefficient maps and field inclusions are the original ones; the proof
changes no field norm or topology.

`productPointHomeomorph` takes the product of these comparisons and then
reindexes by `indexEquiv`. Its component formula evaluates exactly the
corresponding factor comparison at each actual upper coordinate.

Assume that `X` is separated and of finite type, that its original Weil
restriction `W` to the lower S-integers is algebraic, and that `W` is
separated and of finite type. `adelicLevelPointHomeomorph` identifies
`W`'s `T`-stage with `X`'s `upperLevel`-stage, both with their defined space
stage topologies. It composes the stage-to-original-upper-factor Weil
homeomorphism, `productPointHomeomorph`, and the inverse of the upper
space stage coordinate homeomorphism. Quasi-separatedness of `X`, needed
by the local Weil comparison, follows from its separatedness.

`adelicLevelPointHomeomorph_coordinates` proves that evaluation of the
constructed upper stage point gives exactly the regrouped original local
Weil components. Its proof cancels the upper stage coordinate equivalence
with its inverse. Together with the preceding stage and product component
formulas, this retains the original local tensor counit maps and original
level projections.

The provenance is internal composition of the published actual-place
reindexing, original fixed-model Weil stage comparisons, and space stage
coordinate homeomorphisms. Representability and separated finite-type
geometry of the original Weil model remain explicit inputs. This unit does
not prove compatibility with the full adelic tensor map, the final topology
comparison, or independence of arbitrary models.
