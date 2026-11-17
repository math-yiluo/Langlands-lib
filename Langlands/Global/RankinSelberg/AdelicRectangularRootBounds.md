# Finite-place support bounds for actual adelic rectangular charts

This internal module specializes the local rectangular root estimates to
the project's actual adele ring, its finite-place projections, idelic
diagonals, and standard compact subgroup.
`finiteSimpleRootRadius F r c v` is the maximum of one and the norm of
the tuple of all adjacent idelic ratios at `v`.

The module first proves that entrywise coefficient maps preserve
`lowerBlockPair g x 1`, extension of the rectangle by zero rows, and the
three-block chart with one final identity row. For that final rank the
two natural associations of the indices agree definitionally.

An adelic standard compact matrix has entries of finite-place norm at
most one, as does its inverse. This follows directly from its published
finite integral subgroup membership. Projecting a factorization
`lowerBlockLocalization 1 g x 1 = U*diag(c)*K`, with upper unitriangular
`U` and standard compact `K`, therefore meets the hypotheses of the
ultrametric local estimate. The diagonal of the projected triangular
factor is the projected tuple `c`. Its trailing adjacent ratios are
bounded by `finiteSimpleRootRadius`, giving
`‖x_ij,v‖ ≤ finiteSimpleRootRadius^(d*(d+1))`.

If all the simple-root coordinates are integral at a finite place, the
radius is one, so every rectangular coordinate is integral there as
well. The constant is exactly one, independent of the rank. In
particular the implication can be applied at every place outside a
chosen finite set.

Every factorization hypothesis is explicit. This module gives the
finite-place coordinate estimate; the common global denominator,
archimedean rapid decay, and Mellin convergence remain separate
obligations.
