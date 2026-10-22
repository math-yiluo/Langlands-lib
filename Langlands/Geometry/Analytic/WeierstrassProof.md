# Analytic Weierstrass division and preparation

Author: Worker 56.

`RestrictedSeries.weierstrass` proves `WeierstrassStatement A` by applying
the two constructed distinguished-series theorems in
`DistinguishedNormalization`.

Polynomial division first gives norm-controlled polynomial quotients and
remainders. Polynomial truncations converge in the Gauss norm, so the
division operators extend to restricted series. A contraction corrects
division by a monic polynomial to division by a perturbation of norm less
than one. Norm attainment makes the tail of a normalized distinguished
series such a perturbation.

Dividing `X^d` by the normalized distinguished series produces a quotient
whose difference from one has norm less than one. The convergent geometric
series constructs its inverse. This gives the unit and monic polynomial
in preparation; the uniqueness of division gives uniqueness of these
factors. Finally, multiplication by the inverse of the actual
distinguished coefficient reduces a general distinguished series to the
normalized case. The multiplicative coefficient norm verifies all bounds
after this change.

The proof uses the actual restricted-series norm, polynomial inclusion,
and unit group. It assumes no division or factorization data. The precise
hypotheses and original-source correspondence are in
`WeierstrassStatement.md`; this proof route uses a contraction and the
geometric series to construct the analytic outputs.
