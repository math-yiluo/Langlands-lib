# Determinant twists in rectangular Whittaker integrals

`rectangularMellinIntegral` is the extended nonnegative integral of a function
along the rectangular chart and then over the smaller Whittaker quotient,
with the published measures and the weight `|det h|^σ`. Its value may be
infinite. The definition requires a number field and `t < r`; it needs no
additive quotient compactness assumption.

This internal helper uses the published rectangular matrix chart. Its
determinant is the determinant of its upper left general linear block:
the other two diagonal blocks are identities. The proof passes through
the adelic matrix equivalence, removes the simultaneous reindexing of
rows and columns, and applies `GeneralLinear.det_lowerBlockLocalization`.
Applying the idelic absolute value gives `detNorm_rectangularPoint`.

`rectangularMellinIntegral_norm_le` bounds the Mellin integral of the norm of
a complex function by the majorant at the shifted exponent.
`rectangular_mellin_lt_top_of_majorant` then transfers convergence from a
gauge majorant to a complex function `W`. If
`‖W(g)‖ ≤ |det g|^β Ξ(g)`, the inner integral is bounded by
`|det h|^β` times the integral of `Ξ`, because the determinant does not
depend on the rectangular variable. Pulling out this finite constant
and combining real powers changes the outer exponent from `σ` to
`σ + β`. Monotonicity of the two lower integrals completes the proof.
No measurability of an arbitrarily chosen quotient representative is
needed in this lower integral comparison.

The helper assumes convergence of the majorant at the shifted exponent;
it does not prove gauge convergence.
