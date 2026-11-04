# Finite coordinate series for the actual diagonal kernel

This internal construction enumerates the full refined inverse-image subgroup
schemes from `TriangularCoordinateSubgroups`. For any representation `ρ` of
size `N`, `seriesScheme ρ t` is `filtrationScheme ρ (t / N) (t % N)`, and
`seriesHom` is its actual closed inclusion in the source group scheme.
The finite series uses the indices from `0` through `N * N`, inclusive.

`W_zero_eq_blockUnipotentSubgroup` identifies the first matrix term with the
block-unipotent subgroup for weights `i ↦ -i` over any commutative ring.
`mem_W_zero_iff_projection_eq_one` identifies its membership, within the
triangular matrices, with the kernel of the actual block diagonal projection.
Using the all-test formula for `blockLimitHom` and the monomorphism of the
block Levi inclusion, `filtration_zero_eq_diagonal_kernel` identifies the
first inverse-image term with the full scheme-theoretic diagonal kernel.
`range_seriesHom_first` gives the same identification for the enumerated
series. These equalities quantify over every scheme over the original base.

`range_seriesHom_index` identifies the term at `a * N + b` with the refined
term `(a,b)` when `N > 0` and `b < N`. `range_seriesHom_succ` identifies the
successor with the next row cutoff, including the passage to the next
superdiagonal. It uses the previously proved equality of the full subgroup
functors at `(a,N)` and `(a+1,0)`. `seriesHom_succ_le` proves the adjacent
inclusions when `N > 0`. For a representation monic on underlying relative
schemes, `range_seriesHom_last` proves that the term at `N * N` is the full
trivial subgroup functor. Its proof treats `N = 0` separately and imposes no
positive-size assumption on the endpoint result. The `N = 0` finite series
has a single term. For an actual triangular homomorphism, every enumerated
term is normal by `isNormal_seriesHom`.

A row with no position on the next superdiagonal contributes no new
equation. `refinedW_succ_of_out_of_range` proves equality over every
commutative ring, and `range_seriesHom_succ_of_out_of_range` transfers that
equality to the full inverse-image subgroup schemes. At a genuine position,
`range_kernel_seriesCoordinate` identifies the successor term with the range
inside the original group of the full scheme kernel of the actual additive
coordinate on the current term. The coordinate is the map already constructed
in `TriangularCoordinateMaps`; its column is `t % N + t / N + 1` and its row
is `t % N`.

All constructions retain the original coefficient rings and full subgroup
schemes. There are no smoothness, connectedness or reducedness assumptions.
This is an internal derivation from the explicit matrix filtration, its
represented full inverse images and the existing block projection formula.
It constructs no quotient schemes, descends no conjugation action and proves
no splitting section; those remain obligations of the parent task.
