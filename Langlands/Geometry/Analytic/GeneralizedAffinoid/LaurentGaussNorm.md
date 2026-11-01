# Multiplicativity of the Laurent Gauss norm

Author: Worker 84.

This internal supporting construction proves multiplicativity of the existing
Laurent Gauss norm at every positive real radius over every ultrametric normed
field. It defines the corresponding bounded multiplicative spectrum point on
the completed Laurent algebra. No independence from the value group is assumed.

The proof identifies ordinary polynomials with Laurent polynomials and checks
that the existing norm is Mathlib's polynomial Gauss norm. Multiplication by
an invertible Laurent monomial rescales the norm by the corresponding radius
power. After shifting the two factors to ordinary polynomials, Mathlib's
polynomial Gauss-norm multiplicativity gives the Laurent assertion. Completion
density then gives multiplicativity on the completed algebra.

This does not make the completion a field at a dependent radius, construct a
Gauss section for general affinoid coefficients, or prove finite rational domain
coverage. Its provenance is the explicit comparison and Mathlib proof described
above, rather than a claim to formalize a numbered external result.
