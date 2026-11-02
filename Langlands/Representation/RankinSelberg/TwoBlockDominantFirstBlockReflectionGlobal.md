# Global reflected first-block averages

This module is derived analytic infrastructure for JPSS, *Rankin–Selberg
convolutions* (1983), Section 4.9, printed pages 416–418, particularly equation
(8) on page 418, and Section 4.10(2), page 419. It specializes the existing
exact lower slice tower and the reflected-average Fubini bridge to the actual
lower kernel. Its measurable-kernel formulation and almost-everywhere
convergence transfer are internal derivations.

Write a = m 0 + 1, b = m 1 + 1 and rho = q^(-(d*b)). Fix a two-block shape,
arbitrary natural j and k, the supplied additive Haar measure, inverse-character
block functionals, an induced section, and a large Whittaker function.
`firstBlockReflectedQuotientAverage` is the function Q on the actual lower
mixed quotient given by rho times the lower first-block average, on small
determinant slice d, of the actual lower quotient kernel at spectral
parameter zero. It uses the supplied small quotient measure and its
norm-one right invariance.

`firstBlockReflectedQuotientAverage_analysis` assumes smoothness of the large
representation and first block representation, and takes the large Whittaker
function from the supplied coefficient model. It accepts a sigma-finite
compatible small unipotent quotient measure, a compatible lower mixed
quotient measure, and a compatible lower unipotent quotient measure. On
determinant slice d of the latter it assumes integrability of the actual
lower quotient kernel and its raw norm profile, and almost-everywhere
integrability of its product-rectangle fiber.

The conclusions are that Q is measurable on the whole lower mixed quotient
and integrable on its determinant-zero slice. Almost everywhere on that
slice, for every group representative g of the base point, the actual
reflected smaller coefficient is integrable in the j-by-b variable Y, and
its Y integral equals Q at that point. Finally the integral of Q over the
lower mixed determinant-zero slice equals the actual lower quotient-kernel
integral over determinant slice d, with the supplied measures unchanged.
Zero functionals and zero row counts are included.

The proof uses the exact identity
`ofReal rho • (firstBlockKernel ∘ₘ lowerMixedZeroSlice) = lowerSlice d`.
Positivity and finiteness of the density transfer integrability to the
composed measure. Kernel composition then gives integrability of the raw
norm profile and the raw fiber convergence almost everywhere in each small
quotient fiber. On group representatives the kernel is the pushforward
along the actual first-block fiber map, so the reflected product-control
theorem applies. Compatibility supplies regularity of the small measure,
making the first-block kernel s-finite; integrating that kernel proves
measurability and integrability of its average. The kernel integral formula
and the same exact measure identity prove the last equality.

The theorem retains its explicit convergence assumptions. It does not derive
their representation-theoretic existence or integrate a Laurent identity.
