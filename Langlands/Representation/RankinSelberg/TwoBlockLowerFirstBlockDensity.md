# Determinant density for the lower first-block slice

This is derived support for Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg Convolutions* (1983), Section 4.9, equation (8), printed page 418,
registered as `jpss-1983-rankin-selberg`. It identifies the explicit density
required by the linked lower mixed quotient integration statement.

For every canonical p-adic field, small rank `n + 1`, natural exponent `b`,
and integer slice index `k`, `FirstBlockDensityStatement` states that

`d = ENNReal.ofReal (q ^ (-(k * b)))`

is strictly positive and finite, and equals
`(ENNReal.ofReal (|det v|)) ^ b` for every representative `v` of the small
determinant slice of order `k`. The field structures and normalized absolute
value are the canonical ones. In the linked target, `n = m 0` and
`b = m 1 + 1`; the exponent is the positive second-block dimension.
The support statement also allows `b = 0`, where the formula still holds.

The implemented proof `firstBlockDensity` uses the residue cardinality's
strict positivity to prove positivity of every integer power. Every `ofReal`
value is finite. The published representative slice characterization gives
`|det v| = q ^ (-k)`, and the integer-power multiplication law and
compatibility of `ENNReal.ofReal` with natural powers give the claimed
coefficient. This proof has no quotient measures, representation hypotheses,
or convergence assumptions. It establishes the density clause only; the
slice measure identity and its analytic consequences are separate obligations.
