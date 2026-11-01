# Matched adjacent finite-product functional equation

Worker 486. This internal composition defines the Prop-valued
`AdjacentRankCorankFunctionalEquation`: actual original and dual corank-one
integrals admit rational continuations satisfying one normalized equation,
with fixed polynomials, complex units and Laurent exponent. Both pole guards
of `NormalizedFunctionalEquation` are retained. The sign exponent is the
ambient corank index `r+1`.

`adjacentRankModel_matchedNormalizedFunctionalEquation` proves this predicate
for a specified separated coefficient of an actual ambient full
Whittaker-type model. It assumes full type and specified nonzero functionals
on the block, test and ambient representations; an actual row Fourier pair;
the stated separated-model integral identity; equal-rank normalized equations
with fixed data; the test model-minus-one scalar; and literal matrix equation
witnesses with fixed data. Its conclusion uses product polynomials `P0*P1`
and `PD0*PD1`, epsilon unit `c0*c1`, and exponent `m0+m1`.
The carrier universes of the field, block, test and ambient representations
are independent. The supplied scalar self-dual measure and compatible
quotient measure are unchanged.

The proof calls `adjacentRankModel_matchedProductContinuation` to obtain one
finite family of actual test-model coefficients and actual bi-smooth matrix
coefficients. It applies the supplied matrix-witness predicate to those same
matrix coefficients, choosing their original and unreflected dual rational
values. `adjacentRankMatrix_reflectedRationalValue` and the actual
model-minus-one identity convert these dual values to the reflected tests
needed by the model-star formula. Thus the original and dual continuation
formulas use the same finite family throughout.

For each equal-rank factor, the supplied equation chooses a Fourier test.
Uniqueness of the actual Fourier pair identifies it with the specified row
Fourier test. Rational-continuation uniqueness identifies both rational
values with the corresponding values in the matched continuation formulas.
`adjacentRank_reflectedFiniteProducts_functionalEquation` then cancels the
recorded model-star and reflection scalars and combines the finite products.
It yields precisely the ambient sign exponent `r+1`, including when summand
poles cancel in the finite sum.

Provenance is internal composition of these imported proofs. The theorem
retains the equal-rank and matrix equations as explicit premises. It proves
the equation only for a separated coefficient; whole-image extension,
gamma-factor comparison, large-twist continuation and the arbitrary-input
parent gamma theorem remain separate obligations.
