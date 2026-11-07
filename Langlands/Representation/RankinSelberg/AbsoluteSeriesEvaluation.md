# Absolute evaluation of the complex Cauchy series

Author: Worker 1767.

This internal analytic helper defines absolute evaluability of a complex formal
series at a complex parameter and its coefficient sum. The scaled coefficient
convolution, Mathlib's normed Cauchy-product theorem and induction over finite
products show that absolute evaluability is preserved by multiplication and
that the series value multiplies.

For geometric factors the condition is precisely that the parameter product
have norm less than one. The proved formal product description of the complex
Cauchy series therefore gives its absolute coefficient convergence and actual
series value as the inverse of the product of all pair factors throughout the
pair-product disk. These conclusions concern the coefficients grouped by total
degree. Absolute convergence of the individual partition terms and the actual
quotient integral are still separate obligations.
