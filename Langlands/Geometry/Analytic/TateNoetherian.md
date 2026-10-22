# Noetherianity of genuine Tate algebras and their presented quotients

Author: Worker 56.

The proof proceeds by induction on the number of Tate variables. In zero
variables, the proved surjectivity of the scalar map transfers the
Noetherian property of the coefficient field. For a nonzero ideal in the
induction step, choose a nonzero element and apply the actual coordinate
construction. The transported ideal contains a distinguished series in
one variable over the smaller Tate algebra.

The principal-ideal quotient by that series is finite over the smaller
Tate algebra, by the constructed analytic division remainders. It is
therefore Noetherian by the induction hypothesis. The image of the
transported ideal in this quotient is finitely generated, and its
intersection with the quotient kernel is the principal ideal itself.
Mathlib's finite-generation lifting theorem now proves that the transported
ideal is finitely generated. Mapping its generators back through the actual
ring equivalence proves the same for the original ideal.

This establishes the Noetherian property for every finite-variable Tate
algebra over a complete ultrametric normed field. It then descends through
the genuine quotient presentation map to `PresentedStrictAffinoidAlgebra`,
including a zero quotient. No ideal-closedness or factoriality theorem is
asserted here. The quotient construction still uses the closed ideal
specified by the presentation to obtain its norm.

The proof implements the induction underlying Proposition 2.3.2(i),
page 5, and Corollary 2.3.3, page 6 of the retained Berkovich-course notes.
The source first reduces to a Weierstrass polynomial and identifies its
quotient with a polynomial quotient. Here
`isNoetherianRing_tate` directly uses
`RestrictedSeries.finite_quotient_of_distinguished_mem`, whose analytic
division proof supplies finite generation for the distinguished-series
quotient. Mathlib's `IsNoetherianRing.of_finite` then gives its Noetherian
property. This is a derived proof route with the same induction, and
uses no assumed Rückert structure. The quotient instance is the usual
surjective-image consequence, including when the quotient is zero.
The coefficient valuation may be trivial.

Source `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
The retained source is
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`,
“2. Affinoid algebras,” notes of part of Vladimir Berkovich's course.
The note-taker and publication date are unidentified.
