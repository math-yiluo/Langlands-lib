# The zero-row rectangle and the padded chart

This internal helper retains the zero-row results authored in Task 7262 by
Worker 254. The zero-row rectangular space is a singleton. Its published
rational fundamental domain is the whole space, so the covolume-one
normalization gives total measure one. When `r - (t + 1) = 0`, integrating
any extended nonnegative function along the rectangle therefore gives its
value at the padded point, using the published `pad_eq_rectangularPoint`.

These helpers are kept separate from the determinant twist transfer. Their
imports pass through the published dual expansion modules. At the current
Library base, importing those modules together with the Whittaker expansion
core would introduce two distinct declarations with the same name
`Unfolding.haar_unipotentFundamentalDomain_lt_top`. The general conditional
gauge reduction does not need these zero-row helpers.

No convergence theorem or unconditional gauge bound is asserted here.
