# Polynomial functions in a real ascending tail kernel

The nonzero-weight ascending tail maps the two position characters of a real induced block onto that block in the compact-finite standard module. `ascendingTailKernel_polynomial` shows that each vector in its kernel is polynomial of degree less than the absolute weight along left translation by the simple lower root inside the block. The assertion holds through every group element and with arbitrary surrounding blocks.

The binomial map from the descending pair has nonzero multipliers on the low modes of the correct parity. The tail has nonzero multipliers on the high modes. The pointwise inverse of the binomial multiplier recovers every vector killed by the tail from the range of the binomial map. The upper and lower position exponents differ by the absolute weight, and the binomial window gives the lower-root power relation for the associated Jacquet functional. Evaluation of its Frobenius function after compact translation gives the vanishing Taylor coefficient on the orthogonal group. `realTaylorLeftPolynomial` propagates that condition to all group elements and produces the polynomial.

This is an internal consequence of the adjacent Fourier multipliers and the lower-root Taylor theorem. The polynomial kernel condition allows comparison of the exact Whittaker spaces before and after the tail quotient.
