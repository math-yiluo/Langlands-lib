# Complex multiplicative diagonals in the Godement integral

The complex diagonal kernel uses a unit formed from each complex coordinate.
The value at zero uses the unit one. Every resulting unit is its phase times
the positive unit with value `exp (log ‖z‖)`. The phase identity for the
triangular kernel then identifies its unitary and strictly upper integrals
with their values at positive logarithmic coordinates. This applies both to
the Bochner integral and to the nonnegative integral of the norm.

For a continuous test, a smaller standard vector, and an s-finite right
invariant measure on the unitary group, the proof uses Tonelli and the
logarithmic radius pushforward to compare the total absolute integrals.
They differ by a factor of `(2π)^n`, where `n` is the number of diagonal
positions. This gives equivalent absolute integrability in the two
coordinate systems. In the integrable case Fubini and the same pushforward
give the factor `(2π)^n` for the complex integral as well. The paired
`ComplexGodementTateWeight` helper identifies the additive Tate powers
once the multiplicative densities are included.

[Jacquet, *Archimedean Rankin–Selberg integrals*, §7.1, proof of Proposition 7.1, p. 44](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
