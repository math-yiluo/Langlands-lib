# Continuity from the actual finite Banach presentation

Author: Worker 56.

Let K be a nontrivially normed field, A and B complete normed
K-algebras, and B a finite A-algebra with continuous structure map.
For a normed A-algebra C with continuous structure map, the implemented
theorem proves that every A-algebra homomorphism B to C is continuous.
When C is also a normed K-algebra with the compatible scalar tower,
the theorem returns a global linear norm bound.
Neither completeness of K nor completeness of C is required.

The proof selects actual finite generators of B as an A-module.
Their finite linear-combination map from a finite product of A is
surjective and continuous: it is a finite sum of products of continuous
coefficient maps and fixed generators. As a map of Banach K-spaces,
Mathlib's Banach open mapping theorem proves it is a quotient map.
Composing the given algebra homomorphism with this quotient map gives
the same finite sum with the images of the generators. This composite
is continuous by the hypothesis on A to C. The quotient-map property
therefore proves continuity of the entire homomorphism. Its continuous
K-linear operator norm supplies the final bound.

This is an auxiliary analytic argument for the finite-normalization
step in the domain case of Proposition 2.6.1, page 11, and Proposition
2.6.4, pages 11-12, of the retained Berkovich-course notes. The Lean
proof uses the Banach open mapping theorem directly; it does not invoke
the notes' stronger finite Banach-module statements as assumptions.
Nontriviality of the valuation is essential to this implementation
route. The trivially valued case is treated separately elsewhere.

`GaussAlgebraicClosure` constructs the normed field extension used by
`SpectralMinpoly`, which applies this continuity result to bound the
coefficients of the minimal polynomial.

Source: `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
retained PDF SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
The actual formal ingredients are Mathlib's
`Module.Finite.exists_fin`, `Fintype.linearCombination`,
`ContinuousLinearMap.isQuotientMap`, and the operator-norm bound.
