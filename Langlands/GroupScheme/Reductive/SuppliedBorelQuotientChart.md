# Actual supplied central quotients in Borel-adapted coordinates

This internal construction uses the full centre's arbitrary-base-change
and isomorphism transport, actual fppf-quotient transport, and
`AffinePinnedModel.adjointQuotientChartOver`. It asserts no new external
source theorem.

A `SuppliedTorusAffineChart` expresses the actual supplied quotient map in
its coordinate torus. `centralKernel_eq` identifies its whole transported
kernel subgroup functor with the inverse image of the model's full centre
under the actual coordinate inclusion. It uses the exact inclusion square
and invariance of all-test centrality under the actual ambient isomorphism.
No reduced, connected or saturated centre replaces that subgroup. Thus
`quotientMap_isFppfQuotient` retains the full fppf quotient predicate.

On any scheme mapping to the affine model, the actual group and torus
isomorphisms are pulled back and normalized by the canonical direct-versus-
iterated pullback comparisons. Their exact inclusion square is preserved.
`quotientMapOver` is the direct original supplied quotient preceded by
this actual coordinate torus isomorphism. Naturality identifies it with the
normalized iterated pullback, and it remains a full fppf quotient of the
explicit transported original central subgroup.

`quotientChartOver` gives an actual isomorphism from the direct supplied
quotient pullback to the split torus indexed by any supplied root base's
simple-root support. Its exact factorization is the character projection
with exponent vectors equal to those same simple roots. The base scheme
and its map to the model are arbitrary.

`SuppliedBorelChart.quotientChart` chooses the root base and open restriction
already adapted to the actual supplied Borel. Its factorization uses those
simple roots and the same supplied quotient. Overlap permutations, atlas
assembly and the final Weil presentation remain outside this pair.
