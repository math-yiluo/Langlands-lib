# Original upper-place regrouping of curve-place space Weil stages

This internal construction compares actual enlarged arithmetic stages of
a fixed principal curve S-integer space model and its Weil restriction.
It uses the original upper-place indexing and original field-valued point
topologies and includes inseparable finite extensions.

Let `k` be a finite field and `K` and `L` global function fields over `k`
with their specified rational-function-field algebra structures and a
compatible finite extension `L/K`. Choose `s` with `K` finite-dimensional
over `k(s)` and a nonzero `t` in the corresponding chart ring. Let `T`
contain the principal exceptional support determined by `s` and `t`.
The upper initial support is its full preimage in `L`, and `upperLevel`
is the full preimage of `T` viewed above that upper initial support.
`indexEquiv` is the published bijection from pairs of lower coordinates
and upper places above them to the actual upper-level coordinates.

For an algebraic space `X` over the fixed upper coefficient ring,
`factorPointHomeomorph` compares the point space at each original upper
local factor with the same factor in the upper arithmetic stage. Each has
its original field-valued topology; at an integer coordinate this topology
is induced through the original inclusion into the completed field. Case
analysis on field and integer coordinates reduces these comparisons to
identity homeomorphisms. No norm or point topology is changed.

`productPointHomeomorph` takes the product of these comparisons and reindexes
by `indexEquiv`. Its component formula evaluates the corresponding factor
comparison at the original upper coordinate.

Assume that `X` is separated and of finite type, that its Weil restriction
`W` to the original lower S-integers is algebraic, and that `W` is separated
and of finite type. Assume that the lower principal exceptional support
is nonempty. `upperSupport_nonempty` derives nonemptiness of its full upper
preimage by choosing a lower place in the support and applying surjectivity
of the original restriction map on places. No additional nonemptiness
premise is imposed on the upper support.

`adelicLevelPointHomeomorph` identifies `W`'s `T`-stage with `X`'s
`upperLevel`-stage, both with their defined space stage topologies. It
composes the lower stage-to-original-upper-factor Weil homeomorphism,
`productPointHomeomorph`, and the inverse upper space stage coordinate
homeomorphism. Separatedness of `X` supplies the quasi-separatedness needed
by the local comparison. The two nonempty support facts permit the curve
stage coordinate bijections on both sides.

`adelicLevelPointHomeomorph_coordinates` proves that upper-stage coordinate
evaluation of the constructed comparison is exactly the regrouped original
local Weil components. The proof cancels the last coordinate equivalence
with its inverse. Together with the preceding component formulas this
retains the original tensor counit maps and original enlarged-level
projections.

The provenance is internal composition of the actual-place reindexing,
fixed-model curve Weil stage homeomorphisms, place-restriction surjectivity,
and space stage coordinate comparisons. Original Weil algebraicity and the
separated finite-type geometry of both models remain explicit. This unit
does not prove compatibility with the full adelic tensor map, the final
topology comparison, or independence of arbitrary models.
