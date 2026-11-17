# The rectangular Whittaker bound from analytic gauge inputs

This is an internal conditional helper for `UnequalRectGaugeStatement`.
For a fixed cuspidal realization it takes a common determinant exponent
`β`, a common gauge exponent `τ`, and pointwise gauge majorants for every
standard additive character and vector. It also assumes the separate
rectangular Mellin convergence statement.

Apply that convergence statement once to obtain `C`, common to all
gauges of exponent `τ`. The definition `rectangularGaugeThreshold C β`
is `max 0 (C - β)`. Its nonnegativity and the strict inequality
`C < σ + β` for every larger `σ` are proved separately and used for the
required Whittaker threshold. The
pointwise majorant for the chosen character and vector satisfies gauge
convergence at this shifted exponent. The proved
`rectangular_mellin_lt_top_of_majorant` supplies the desired iterated
Whittaker integral bound.

Both exponent uniformities are preserved: neither `C` nor `β` nor `τ`
depends on the character or vector. This helper does not establish either
of its analytic inputs and is not an unconditional proof of the target.
The gauge and rectangular Mellin proposition definitions are published
Library interfaces; neither analytic conclusion is assumed proved here.
