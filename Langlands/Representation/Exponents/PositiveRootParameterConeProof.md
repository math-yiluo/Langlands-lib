# Strict cone comparison in flattened coordinates

This module proves the published proposition
`Langlands.Exponents.PositiveRootParameterConeStatement` with theorem
`Langlands.Exponents.positiveRootParameterCone`.

`reindex_roots` reindexes the published natural-index simple-root sum by
`j ↦ j+1`, identifying it with the actual adjacent fine indices.
`cone_iff_adjacent` applies the existing simple-root characterization in
`Exponents.Chambers` in both directions. It retains strict positivity of
every adjacent coefficient, including the vacuous empty family.

`size_cancel` cancels a nonzero fine size in one scalar root. The proof of
`parameter_iff_cone` applies that cancellation inside each finite sum. In
the reverse direction, the adjacent coefficients are chosen for each
original block and multiplication by its positive fine sizes is canceled.
No flattening index is replaced: all values of the given parameter are
evaluated through `D.flattenBlockEquiv R`.

The final theorem assembles this equivalence for all ranks and refinements.
This is internal finite linear algebra suggested by Worker 156; it uses no
analytic or representation-theoretic support theorem.
