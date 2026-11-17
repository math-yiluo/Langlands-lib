# Product majorants for dominated adelic rows

This internal helper derives a product bound from the published
`EqualAnalytic.IsRowDominated` condition and the internal Schwartz majorant
construction of `AdelicRowMajorant`. It makes no new convergence assumption.

For a row function of positive length `n`, index a family by a row `x` and
one coordinate `j`. Its rank-one row is the constant one-entry row `x_j`,
and its weight is `‖Φ(x)‖^(1/n)`. The archimedean norm of this row is at
most the norm of the original row. The original rapid bound of order
`N*n`, followed by taking a nonnegative `n`th root, bounds the weighted
rank-one family at order `N`. Its finite support uses the same rational
denominator as the original function.

The Schwartz majorant construction therefore supplies one rank-one
Schwartz–Bruhat function whose norm bounds every coordinate's weight.
Multiplying the `n` inequalities recovers `‖Φ(x)‖` on the left and gives
the required product bound. The argument needs positive row length but
does not require continuity of the original function.
