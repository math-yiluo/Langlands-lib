# The zero-row rectangle and the padded chart

This internal helper retains the zero-row results of the proof of the
rectangular Whittaker gauge bound (`UnequalRectGaugeStatement`). The zero-row
rectangular space is a singleton. Its Library
rational fundamental domain is the whole space, so the covolume-one
normalization gives total measure one. When `r - (t + 1) = 0`, integrating
any extended nonnegative function along the rectangle therefore gives its
value at the padded point, using the Library's `pad_eq_rectangularPoint`.

These helpers are kept separate from the determinant twist transfer. Their
imports pass through the dual expansion modules. The general conditional
gauge reduction does not need these zero-row helpers.

No convergence theorem or unconditional gauge bound is asserted here.
