# Evaluation through a contractive coefficient algebra map

This module adapts the published weighted evaluation proof of `GeneralizedTateAlgebra.Evaluation`, itself adapting the strict evaluation arguments.

This is a derived auxiliary construction for the relative-series quotient comparison. For a contractive bounded K-algebra homomorphism from an ultrametric normed coefficient algebra A to a complete ultrametric normed algebra B, and a tuple in B whose monomials are bounded by the polyradius weights, evaluation sums the actual coefficient monomials after applying the coefficient homomorphism. No coefficient field or nonzero coefficient algebra is required.

The termwise norm bound proves summability and contractivity. Additivity follows by summing the termwise equality, and multiplicativity follows from the nonarchimedean Cauchy product. Evaluation has the specified values on coefficient constants and variables. Relative monomial factorization and the established convergent monomial expansion also show that bounded algebra homomorphisms agreeing on all coefficients and variables agree everywhere.

This extends the proof pattern of the published scalar `GeneralizedTateAlgebra.Evaluation` module to a specified coefficient homomorphism. It uses the project's definitions and monomial-expansion theorem, rather than an additional result from the original literature.
