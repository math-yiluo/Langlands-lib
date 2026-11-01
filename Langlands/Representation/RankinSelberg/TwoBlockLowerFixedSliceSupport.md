# Integer simple-root support

This internal specialization of `Whittaker.smoothSimpleRootSupport` chooses an
integer upper bound on every consecutive increase of a canonical uniformizer
exponent vector where an actual coefficient-image vector is nonzero.
The bound is uniform over the integral compact factor and uses smoothness only.
The canonical normalized absolute value of a uniformizer power is the residue
cardinality to the negative exponent. Choose an integer power larger than the
existing real support bound, then use strict monotonicity of real integer powers.

`RootBounded.antitone` subtracts the coordinate index times the root bound,
producing an antitone integer sequence. `RootBounded.le_of_le` then propagates
the bound across any interval at cost at most the ambient rank minus one times
the root bound. `oppositeCone_of_endpoints` applies this on the two sides of
one adjacent pair: a lower bound at the end of the initial segment and an upper
bound at the start of its complement yield uniform lower and upper coordinate
bounds, respectively.

`OppositeCone M s lam` records these inequalities for any finite subset `s`
of coordinates. `twistDegree s lam` sums the exponents in `s` and the negatives
of the remaining exponents. On this cone each absolute exponent is bounded by
its signed contribution plus `2 * M`. Summing gives
`torusSize lam ≤ twistDegree s lam + rank * (2 * M)`, with integer casts.
This is elementary finite-sequence geometry derived for the convergence proof;
it asserts no Fourier endpoint bound or integral convergence.
