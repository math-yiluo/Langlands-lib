# Padded simple-root gauge convergence on the diagonal torus

This internal helper applies the multivariable adelic Schwartz Mellin theorem
to the actual diagonal restriction of an adelic simple-root gauge. It proves
convergence on the idele torus, with arbitrary Haar normalization. Passing to
the Whittaker quotient still requires a separate integration comparison.

Let the ambient rank be `r + 1` and the padded block rank be `t + 1`, with
`t < r`. For diagonal entries `d`, use block root coordinates
`a_j = d_j / d_(j+1)` for `j < t` and `a_t = d_t`. The ambient simple-root
row of the padded diagonal is this row of `t + 1` roots followed by ones.
Restricting the gauge's Schwartz–Bruhat function to that affine coordinate
subspace gives a Schwartz–Bruhat function on the active roots.

The gauge's negative scalar power, multiplied by the determinant weight
`|det d|^sigma`, becomes the product of root powers with exponents
`(j + 1) * sigma - tau`. The theorem permits an additional fixed real root
exponent `kappa_j`. Combining powers gives exponent
`(j + 1) * sigma - tau + kappa_j` in each coordinate. If all these exponents
exceed `3`, the multivariable Mellin theorem makes the integral finite.
The continuous multiplicative equivalence between diagonal and block root
coordinates transports this finiteness for any Haar measure on the torus.

The next theorem gives the sufficient uniform bound
`sigma > tau + 3 + sum_j |kappa_j|`. Since the gauge exponent is nonnegative,
this implies `sigma > 0`; each determinant multiplicity `j + 1` is at least
one, and each negative root weight is bounded by the sum of absolute weights.
The final specialization sets every additional weight to zero and obtains
the threshold `tau + 3`. None of these thresholds depends on the choice of
the gauge's Schwartz–Bruhat function.

The result is derived from the coordinate, restriction and Mellin helpers
named in its imports. It asserts no full-group gauge existence theorem and
no quotient integration formula.
