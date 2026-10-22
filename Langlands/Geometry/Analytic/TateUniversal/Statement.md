# Bounded evaluation and the strict Tate universal-property target

Author: Worker 36.

`Langlands.Analytic.StrictTateAlgebra.BoundedUniversalPropertyStatement`
is a proposition definition with four conjuncts. The variable type, coefficient
field and target algebra range over independent universes.

1. For a finite variable type and any normed commutative target ring, a tuple
   has one bound for all its finite monomials if and only if each coordinate
   has a positive uniform bound on all natural powers, including power zero.
2. Over an ultrametric normed coefficient field, a bounded-monomial tuple in
   a complete ultrametric normed algebra has a convergent evaluated coefficient
   series. Its sum is the displayed `evaluate` function, and a bounded algebra
   homomorphism realizes that function and sends every coordinate to the tuple.
   Coefficient completeness is not required for this existence assertion.
3. Over a complete ultrametric normed coefficient field, every bounded algebra
   map's coordinate images have bounded monomials, and two such maps agreeing
   on coordinates are equal. The target here need not be complete or ultrametric.
4. If the coefficient field and ultrametric target algebra are both complete,
   every bounded-monomial tuple gives exactly one bounded algebra map with the
   specified coordinate images.

No nontriviality or norm-one condition is imposed on the target. Empty tuples
and the zero algebra are included. Only the first conjunct requires finitely
many variables. The monomial bound is an explicit inequality for actual products,
not an assumed extension or other output. Evaluation is defined beforehand as
`tsum`; the target asserts its actual convergence under the stated hypotheses.

The source context is Berkovich, Non-archimedean analytic spaces (Trieste 2009),
Example 1.2.2(v), p.4, Definitions 2.1.1-2.1.2, p.7, and Exercise 2.1.5(i),
pp.7-8. This is derived foundational content: the source's affine extension
uses spectral bounds, while this proposition isolates the actual bounded-monomial
hypothesis needed for convergent evaluation. It permits arbitrary variable types
and generic target algebras, and records the precise completeness needed for
existence and uniqueness. No implication from spectral inequalities to power
bounds, nor analytic-domain representability, is asserted. The finite power-bound
equivalence is an elementary internal comparison of the two norm predicates.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The statement imports only the evaluation/coordinate definitions, bounded-algebra
map interface and their intrinsic obligations. It imports neither its proof nor
the separate monomial-expansion proof.
