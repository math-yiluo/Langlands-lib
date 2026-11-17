# Root weights for the actual diagonal conjugation modulus

This internal helper connects the explicit positive-root product used in the
padded Mellin estimate to `AdelicDiagonalUnipotentModulus.diagonalModulus`.
That imported homomorphism is the actual unipotent conjugation Haar modulus.

`gaugeDiagonalInverseHaarWeight` takes its inverse as a nonnegative real
number, then includes it in the extended nonnegative reals. This is the
weight used by the compact torus quotient criterion. The nested positive-root
product formula for the imported modulus identifies its real value with
`gaugeDiagonalModulus`. The coercion commutes with inversion, and the
positive-root product's inverse is already expressed by the fixed real
root exponents `-((j+1)*(t-j))`.

The final theorem therefore restates padded torus convergence with the actual
inverse Haar modulus in place of the explicit product. It keeps the
hypotheses and threshold
`sigma > tau + 3 + sum_j (j+1)*(t-j)`.
Its derivation is the imported modulus calculation, coercion identities and
the previously proved padded Mellin bound. It supplies no integration
comparison with the Whittaker quotient.
