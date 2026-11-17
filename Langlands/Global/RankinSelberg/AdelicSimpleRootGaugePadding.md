# Simple-root coordinates of padded adelic diagonals

This module proves elementary coordinate identities for the proposed
simple-root gauges. It is internal algebraic infrastructure, derived from
the Library's diagonal matrix and padding constructions.

`gaugePaddedIdeles` extends a diagonal tuple by identity ideles.
`pad_gaugeDiagonalPoint` proves that this tuple represents precisely
the padded matrix `diag(g, I)`. The proof uses `adelicEquiv_pad`,
`padGL_apply` and the entry formula for `diagonalMatrixUnits`, then checks
whether the row and column indices lie in the original block.

If `t < r` and the original diagonal has length `t+1`,
`gaugeSimpleRootIdeles_padded` computes every one of the `r` ambient
simple roots. Indices below `t` give the adjacent ratios of the original
tuple. Index `t` gives the original last diagonal idele divided by one.
All later roots are one. The proof splits these three index ranges and
unfolds the adjacent-ratio definition.

`gaugeSimpleRootIdeles_prod` telescopes the adjacent ratios to the
first diagonal idele divided by the last. It compares the two standard
finite-product formulas which omit the last or the first index.
Applying the normalized idelic absolute value and its multiplicativity
gives `gaugeSimpleRootNormProduct_eq`. For the proper padded tuple the
last entry is one, giving `gaugeSimpleRootNormProduct_padded`.

These are exact matrix and group identities. They assert no analytic
convergence or existence of a Whittaker majorant. The gauge definitions are imported from the Library.
