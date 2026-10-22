# Bounded evaluation of Tate series

Author: Worker 36.

Given a family of elements in a complete ultrametric commutative normed
algebra whose finite monomials have one uniform positive norm bound, evaluate each
coefficient monomial by multiplying its scalar coefficient with the finite
product of the supplied elements to the indicated powers. Its norm is at most
a fixed constant times the coefficient norm. Restrictedness and nonarchimedean completeness therefore
give unconditional convergence of the actual evaluated series.

The sum is bounded for the Tate Gauss norm. The bound includes the target
unit norm; no normalized-unit or nonzero-target hypothesis is imposed.
Unit-ball tuples in a target with unit norm one give the contractive special
case. Additivity follows by adding
the summable terms. Multiplicativity uses the nonarchimedean Cauchy product
formula and the finite antidiagonal formula for formal-power-series
coefficients. The finite monomial values multiply by addition of exponents.
Constants evaluate through the actual scalar algebra map. These arguments
construct a bounded algebra homomorphism; no evaluation output is assumed.

For a finite tuple, boundedness of all monomials is also proved equivalent to
boundedness of the powers of each entry. The proof multiplies finitely many
coordinate bounds; the empty tuple is treated separately using the target
unit norm. This avoids silently assuming either a nonempty tuple or a
normalized target algebra.

This is an internal expansion of the convergent-series and affinoid conventions
in Berkovich's Trieste 2009 lectures, Example 1.2.2(v) and Definition 2.1.2.
The TateSeries.Definitions and Affinoid modules supply the monomials, series
norm and bounded algebra homomorphism interface. The raw evaluation data are
in TateEvaluation.Definitions. This proof module does not use completeness of
the coefficient field or the monomial-expansion theorem. The exact combined
target is TateUniversal.Statement; TateUniversal proves uniqueness by coordinate
values using norm-convergent monomial expansion. No affinoid localization
representability is asserted.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The extension context is Exercise 2.1.5(i), pp.7-8; the present hypothesis is
actual bounded monomials, not the source's affinoid spectral bound.
