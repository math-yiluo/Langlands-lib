# Convergent reflected first-block averages

This is derived analytic infrastructure for JPSS, *Rankin–Selberg convolutions*
(1983), Section 4.9, printed pages 416–418, and Section 4.10(2), page 419.
The original calculation motivates the reflected integral and its positive
first-block density. The quotient descent, arbitrary row counts, norm estimate
and Fubini packaging here are internal derivations from the actual kernels and
supplied measures; they do not assert the host Laurent identity.

Write a = m 0 + 1 and b = m 1 + 1. All natural j and k, all block
representations and supplied inverse-character functionals, every induced
section and every Whittaker test are allowed in the definitions. In particular,
zero functionals and zero-sized rectangles are included. The field carries its
canonical topology, valuation and Borel structures. The additive Haar measure
nu is supplied throughout.

`firstBlockReflectedRowAverage` is the actual reflected smaller fiber integral
in the k-by-a rectangle, multiplied by the large-base determinant weight at
spectral parameter zero and by q^d. Its small quotient argument is reflected
by the existing Weyl/inverse-transpose quotient map. The remaining j-by-b
rectangle is denoted Y. `firstBlockReflectedColumnNormProfile` is the integral
over Y of the norm of this average. `firstBlockReflectionDensity` is the real
number rho = q^(-(d*b)); the module proves its nonnegativity.

`continuous_firstBlockDualFiberIntegrand_reflection` assumes continuity of the
large Whittaker function and smoothness of the first block representation.
It descends continuity through the open unipotent quotient map. On group
representatives the reflected integrand is the literal lower test matrix with
first rectangle -w_a*v*z.transpose and second rectangle obtained by reversing
both indices of Y. Smoothness makes the actual first-block matrix coefficient
locally constant. Thus no measurable choice of quotient representatives is
needed. Integrating in z gives joint strong measurability of the reflected
row average in its small quotient and Y variables.

On small determinant slice d, the previously derived fiber calculation gives
that row average at [v] as rho times the integral in X of the actual lower
kernel at I(v)*g and the reversed Y. The theorem
`firstBlockReflectedRowAverage_column_control` assumes genuine integrability
of the actual lower product-rectangle fiber at the corresponding lower quotient
point. Fubini for that product, together with the supplied-Haar invariance of
reversing both indices of Y, proves three conclusions: the reflected row
average is integrable in Y; its column norm profile is at most rho times the
actual lower raw norm profile; and its Y integral equals rho times the actual
lower quotient kernel. The norm estimate uses the triangle inequality before
the product integral is recombined.

`firstBlockReflectedRowAverage_product_control` additionally fixes a supplied
s-finite compatible small quotient measure mu, its norm-one right invariance,
and a large-base representative g. On small slice d it assumes almost-everywhere
lower rectangle-fiber integrability and integrability of the actual lower raw
norm profile pulled back along the first-block fiber map. Joint measurability,
the column norm bound and the product integrability criterion prove genuine
integrability on the small-quotient/Y product. Fubini then proves integrability
in Y of the actual reflected smaller coefficient and identifies its integral
with rho times the actual unweighted lower first-block average at [g]. The
coefficient is rewritten by the existing compatible-measure slice reflection
formula before the integrals are interchanged.

These conclusions are conditional on the stated lower convergence hypotheses.
This module neither derives them from representation-theoretic existence
results nor integrates over the lower mixed quotient. It does not choose
Laurent generators, perform polynomial cancellation or prove the final finite
Laurent identity.
