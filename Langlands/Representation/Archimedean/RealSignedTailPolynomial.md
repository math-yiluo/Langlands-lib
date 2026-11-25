# The spectral sign in canonical tail multipliers

This result tracks the sign in the canonical tail crossings.
For a positive natural number `ell`, `eps` equal to zero or one, and
`ell - 1 - eps` even, `canonical_tail_eq` proves

`tailMultiplier ell eps ((-1)^eps.natAbs) j = sign(j) * P_ell(j)`

whenever `j - eps` is even. Here `P_ell` is the explicit falling-factorial
polynomial `RealTailMultiplierPolynomial.tailPolynomial`, and the integer sign
is cast to the complex numbers. The formula includes `j = 0`.
The reducible parity makes the canonical symmetry the negative of
`(-1)^ell`; negative modes therefore acquire the displayed sign.

`spectralMultiplier` is the finite sum of scalar multiples of mode projections.
For any supplied mode decomposition, its projection formula, composition law
and commutation with polynomial evaluation in the same generator are proved.
`signOperator N hp` uses the scalar `sign(j)` in the rank-three compact model
`RealKTypeCount.degreeLE 3 N`.

The helper `frob_restrict_eq_spectral` identifies the compact restriction of
every actual rank-three `blockFrobMap hdata` with the spectral multiplier of
its input. It assumes that the input restriction has degree at most `N`;
it does not assume that bound for the output. The output is compact finite
and hence belongs to some degree bound. Embedding that bound and `N` into
their maximum lets the proof compare every mode projection using the actual
Frobenius Fourier law. Summing the projections proves equality of the compact
restrictions. Consequently `frob_mem_degree` proves that every such map
preserves the chosen input bound, for arbitrary multiplier data.

`canonical_tail_operator_same_degree` now proves the actual compact-vector
formula

`v(output) = signOperator * P_ell(-i gen) v(input)`

using that same degree bound. It combines the scalar identity, the Fourier law,
the vanishing of off-parity input coefficients and the polynomial projection
formula. `RealSignedTailPolynomialStatement` packages the scalar result and the
existence of the same-degree output vector with this exact operator formula.
`realSignedTailPolynomial` proves the proposition.

The provenance is entirely internal: the explicit existing tail sequence,
its reflection symmetry, compact polynomial mode decompositions and the actual
Frobenius Fourier law. The sign operator is retained explicitly. No relation
between sign operators on adjacent axes, equality of interlaced words, or
filtration kernel-image containment follows from this module alone.
