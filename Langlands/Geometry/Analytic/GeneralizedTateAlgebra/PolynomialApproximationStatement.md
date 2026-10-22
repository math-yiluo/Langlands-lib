# Monomial expansion and polynomial density

Author: Worker 56.

`Langlands.Analytic.GeneralizedTateAlgebra.PolynomialApproximationStatement r K`
has two conjuncts for the actual weighted restricted-series normed ring.

1. Every series is the unconditional sum of its coefficient monomials.
   Mathlib's default `HasSum` means that the finite sums converge to the
   specified series as finite sets of exponents increase under inclusion.
   Each term uses the original series coefficient and the actual monomial
   in `GeneralizedTateAlgebra r K`. Convergence is in the weighted Gauss
   norm, not merely coefficientwise convergence.
2. The polynomial evaluation map has dense range in that normed ring.
   This is the concrete `K`-algebra map `MvPolynomial.aeval` that sends
   each variable to the monomial with coefficient one and exponent one
   at that variable. Scalars map through the existing scalar inclusion.
   Thus the map is specified by actual coordinates, with no supplied
   approximation map or density hypothesis.

The variable type is arbitrary. The radii are arbitrary strictly positive
real numbers. The coefficient ring is any ultrametric normed commutative
ring. Neither conjunct assumes completeness of the coefficients or the
series ring. Empty variable types, a zero coefficient ring, incomplete
coefficients and trivial valuations are allowed. Over infinitely many
variables the finite sets in the first conjunct are finite sets of
finitely supported exponents; no enumeration or degree truncation is
assumed.

The provenance is derived from the carrier and norm in Berkovich,
*Non-Archimedean analytic spaces* (Trieste lectures, 2009),
Example 1.2.2(v), printed/PDF page 4, and the relative formula in
Definition 2.1.6(i), page 8. These passages specify weighted coefficient
decay and the weighted maximum norm; they are not quoted as an explicit
polynomial-density theorem with this generality. The registered original
is `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.
Pages 4 and 8 were read again when preparing this target.

The proposed derivation is that cofinite decay makes the omitted weighted
coefficients uniformly small outside a sufficiently large finite set.
The norm upper-bound criterion then controls the remainder of each
truncation. Finite sums of coefficient monomials are evaluations of finite
polynomials, giving density. This route uses no completeness assumption
and explains the extension to arbitrary variable types and coefficient
rings. For finitely many variables, finite degree-bounded exponent sets
identify the cofinite decay convention with the source's total-degree
escape convention.

This file only defines the proposition to be proved. It neither supplies
its proof nor assumes it as an instance. Completeness, general affinoid
quotient presentations and domain universal properties are separate
obligations.
