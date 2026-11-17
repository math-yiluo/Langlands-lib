# Positive-root modulus in block root coordinates

This internal helper rewrites the product of the positive roots of a diagonal
tuple in adjacent-root coordinates. It is a finite commutative-group identity;
it does not identify a Haar or quotient measure.

`positiveRootProduct` multiplies `d_i / d_j` over all ordered indices `i < j`.
The quotient of the tail products starting at `i` and `j` is the product of
roots from `i` through `j-1`. After substituting this formula, the proof
reorders the three finite products. For a fixed root `k`, its factors are
indexed by `i <= k` and `k < j`. There are `k+1` choices for the first index
and `t-k` for the second, so its multiplicity is `(k+1)*(t-k)`.
The final root has multiplicity zero.

The identity is derived from the block-root equivalence in
`AdelicSimpleRootGaugeTorusCoordinates` and finite-product identities.

`gaugeDiagonalModulus` is the product of the full idele norms of these
positive-root values. Applying the full norm to the group identity gives
its expression as a product of adjacent-root norm powers. Taking inverses
gives the real exponents
`gaugeInverseModulusRootExponent t j = -((j+1)*(t-j))`; the last exponent is
zero. Positivity justifies the real powers and the extended nonnegative
conversion.

The final theorem applies the padded Mellin bound with these fixed
exponents. It proves convergence with the additional inverse-modulus factor
whenever
`sigma > tau + 3 + sum_j (j+1)*(t-j)`.
This threshold depends on the gauge exponent and block rank, but not on its
Schwartz–Bruhat function. The factor here is the explicit positive-root
product; identifying it as a modulus in an integration formula remains a
separate obligation.
