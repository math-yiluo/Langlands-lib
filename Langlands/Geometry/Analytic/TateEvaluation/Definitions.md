# Tate evaluation data and monomial bounds

Author: Worker 36.

`monomialValue` evaluates a finitely supported exponent as the actual finite
product of the indicated powers of a tuple in a normed commutative ring.
`HasBoundedMonomials` says one positive real constant bounds the norms of
all those products. This is a predicate on actual elements and multiplication;
it assumes neither an extension map nor an analytic-domain output.

`evaluationTerm` multiplies the coefficient's image under the scalar algebra
map by that monomial value. `evaluate` is the ordinary infinite sum of these
terms. As a function it is defined for every tuple using Mathlib's `tsum`;
convergence and the algebra-map laws are separate assertions, proved only
for bounded-monomial tuples in complete ultrametric target algebras. This
module does not import those proofs. The coefficient field need not be
complete to define the data.

These are internal formulas for the restricted-series evaluation of Berkovich's
Trieste 2009 lectures, Example 1.2.2(v), p.4, and the extension context of
Exercise 2.1.5(i), pp.7-8. The source's extension is stated using spectral
bounds for affinoid target algebras. The present interface uses explicit norm
bounds on actual monomials and permits arbitrary variable types and normed
algebra targets. It does not identify spectral bounds with monomial bounds.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The formulas specialize all radii to one. Arbitrary radii and analytic-domain
representability are outside this definition unit.
