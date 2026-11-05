# Algebraic bounds under polynomial evaluation and closed immersions

This is a derived algebraic construction for the regular-function definition
`IsAlgebraicallyBounded`. It introduces no topology or finite-type assumption.
The value field has arbitrary universe, and the algebra and evaluation index
may have independent universes.

`boundedEvaluationSubalgebra e` consists of the elements of an algebra whose
values under all the algebra homomorphisms `e i` have a single nonzero valuative
upper bound. Constants are bounded, the valuation inequality and totality
preserve bounds under addition, and products of nonzero bounds bound products.
Polynomial induction then proves that bounded generators give a separate
bound for each polynomial. A surjective polynomial presentation gives the same
conclusion for every algebra element.

The scheme lemmas identify rational-point evaluation with actual pullback on
global sections and the canonical global sections of `Spec F` comparison.
Naturality of the affine canonical isomorphism proves this identification.
Composition of pullbacks proves compatibility with scheme morphisms.
Surjectivity of an affine coordinate pullback therefore transports bounds on
the image of a set to bounds for every regular function on the source.
Mathlib's surjectivity theorem for affine closed immersions gives the final
closed-immersion consequence.

These are internal consequences of the published definition, intended for the
matrix-coordinate argument of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Lemma 2.2.7 (printed p.71, PDF p.102; registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`). They do not assert the spectral
boundedness criterion or derive entry bounds from characteristic polynomials.
