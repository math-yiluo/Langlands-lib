# Isogeny second projections of local-isogeny graphs

This derived certificate construction works over every field and allows an
arbitrary indexing universe for the local family. It retains the actual
local-isogeny graph and both original projection maps.

For a supplied `LocalIsogenyGraphEnvelope D`,
`second_kernel_isFinite_of_maximal_torus` assumes that the graph is connected
reductive, its distinguished source graph torus is maximal, the target
torus inclusion is closed, the target group is separated, and the prescribed
actual torus map is finite. The graph's torus square and
`kernel_isFinite_of_finite_torus_restriction` prove that the full
scheme-theoretic kernel of the second projection is finite.

`second_isIsogeny_of_maximal_torus` further takes flatness, surjectivity and
quasi-compactness of the second projection. The published finite-kernel
criterion for an fpqc homomorphism makes the projection finite; hence it is
an isogeny. No smoothness or reducedness of that kernel is assumed, and no
centrality is concluded.

`IsogenyProjectionGraphEnvelope` records an existing
`ReductiveLocalIsogenyGraphEnvelope`, maximality of its distinguished source
graph torus, and the actual second-projection isogeny.
`isogenyProjectionGraphEnvelope` constructs this certificate from the existing
reductive graph, the displayed maximality and closed target-torus hypotheses,
and finiteness of the prescribed torus map. The existing graph package
supplies flatness, surjectivity and quasi-compactness. The constructor preserves
that package, rather than choosing a new graph or new maps.

The graph reductivity and maximality assumptions remain explicit. This unit
does not prove first-projection invertibility, root-datum base transport, or
the general split reductive isogeny theorem. Its provenance is internal
deduction from the companion full-kernel finiteness theorem, the exact
graph torus square, and the previously constructed graph geometry.
