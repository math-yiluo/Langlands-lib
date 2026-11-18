# Holomorphy of complex equal-rank integrals

The integral of `A(q) exp(s B(q))`, with real measurable `B`, is holomorphic on any open set
where the displayed integrand is Bochner integrable. The proof bounds its parameter derivative
locally by the two integrable weights at real shifts of the parameter. It uses those weights for
dominated differentiation. Integrability of the twisted integrand provides the required almost
everywhere strong measurability, including that of the derivative after multiplication by `B`.

For the complex equal-rank integral, `B(q)` is the logarithm of the squared determinant norm.
Upper-unipotent matrices have determinant one, so this logarithm descends continuously to the
quotient. Rewriting the exact integrand in exponential form establishes holomorphy for it and,
with the dual functions and Fourier-transformed test function, for the dual integral on the
respective convergence domains. This is an internal consequence of the definitions in
`ArchimedeanIntegrals` and Mathlib's dominated differentiation theorem.
