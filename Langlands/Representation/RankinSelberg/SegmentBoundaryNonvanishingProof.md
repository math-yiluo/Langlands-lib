# Proof of centered segment boundary nonvanishing

`segmentBoundaryNonvanishing` proves the existing internal proposition
`SegmentBoundaryNonvanishingStatement`.

The helper `linearFactor_eval_ne_zero` evaluates `1-aX` and uses
`‖az‖ ≤ ‖z‖ < 1` to exclude `az=1`. For a boundary index
`j : Fin (n+1)`, the length order gives the nonnegative integer exponent
`m+n-2j`. The norm of the corresponding power of `t` is at most one.
Multiplying by the supplied parameter preserves this bound, so every boundary
factor has nonzero evaluation. Finite products first over `j` and then over
the parameter set give the conclusion, including the empty parameter set.

The additional constant-coefficient lemma evaluates the boundary product at
zero, where every factor equals one. All results are elementary internal
consequences of the existing normalized linear factors; no
representation-theoretic formula or parameter estimate is assumed implicitly.
