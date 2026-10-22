# Weighted monomial bounds and series evaluation formulas

Author: Worker 56.

`GeneralizedTateAlgebra.HasBoundedMonomials r B b` says that one positive
real number `C` bounds the norm of every actual finite monomial in the tuple
`b`, after dividing by its positive weight `r.weight d`. Explicitly, the
inequality is `norm (b^d) ≤ C * r.weight d`. The finite product is the existing
`StrictTateAlgebra.monomialValue`; the formula for this product does not
involve radii. The condition includes the zero exponent, so it bounds
`norm 1` without requiring `NormOneClass B`. It assumes no evaluation map.
At unit radius the predicate is equivalent to the existing strict predicate,
as proved in `hasBoundedMonomials_unit`.

`X r K i` is the existing coefficient monomial with exponent one at `i` and
coefficient one. Its exact norm is `norm (1 : K) * r i`; when the coefficient
ring has norm-one identity this equals `r i`. The proof uses the exact
monomial norm and the weight of a single-coordinate exponent.

`evaluationTerm` is the product of the actual coefficient's scalar image
with the tuple's finite monomial. `evaluate` is the ordinary `tsum` of
these terms. It is defined as a function for every tuple; this definition
makes no convergence claim. Summability, bounds, algebra-map laws and
uniqueness are separate proof obligations. The formulas need only an
ultrametric normed commutative coefficient ring and a normed commutative
target algebra; no completeness or continuity of the scalar map is needed
to define them. Variable, coefficient and target universes are independent.

For a normed field and a normed target algebra, the evaluation terms and
their sums at unit radius are definitionally the published strict formulas
under `unitAlgEquiv`. The two comparison lemmas assert these identities,
including for tuples for which no convergence theorem has been supplied.
All variable types are permitted, and the target may be the zero ring.

These are internal formulas for the positive-polyradius restricted-series
evaluation described by Berkovich, *Non-Archimedean analytic spaces*
(Trieste lectures, 2009), Example 1.2.2(v), page 4, and the extension context
of Exercise 2.1.5(i), pages 7–8. Definition 2.1.6(i), page 8, supplies the
relative weighted-series formula. These pages were read directly. The
source states its extension using spectral bounds for affinoid targets;
this interface instead uses explicit weighted norm bounds on actual
monomials and allows arbitrary variable types and normed algebra targets.
It does not identify those two conditions. General relative affinoid
presentations and analytic-domain representability remain separate work.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.
