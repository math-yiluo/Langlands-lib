# Unique factorization in the actual finite-variable Tate algebra

Author: Worker 56.

The preliminary algebraic lemma constructs a monic prime factor of any
nonunit monic polynomial over a unique factorization domain. It first
takes an irreducible polynomial factor. The product of the leading
coefficients is one, so these coefficients construct an actual unit.
Multiplication by the corresponding constant units makes both factors
monic without changing the prime factor's associated class.

For Tate algebras, the proof is by induction on the variable count. The
coefficient field is complete and ultrametric, with possibly trivial valuation.
The theorem `uniqueFactorization_tate` applies for every variable count. The
zero-variable algebra is actually isomorphic to the coefficient field.
In the induction step the already proved Noetherian property provides
well-founded divisibility. It is enough to prove that every irreducible
series is prime.

The actual coordinate automorphism and analytic preparation send that
series to a unit times a monic unit-ball polynomial over the smaller Tate
algebra. Take a monic prime factor using the induction hypothesis. The
proved Gauss norm argument keeps this factor in the unit ball, and the
constructed polynomial/analytic quotient equivalence proves that its
analytic image is prime. Since it divides the irreducible analytic
polynomial, the two are associated. Primality transfers through these
associations and the original ring equivalence.

The domain structure is inherited from the actual restricted subalgebra
of formal power series over the field. No factoriality, polynomial quotient
equivalence, preparation, or distinguished-coordinate output is assumed.

This implements the argument of Proposition 2.3.2(iii), pages 5-6,
applied in Corollary 2.3.3, page 6 of the retained Berkovich-course notes.
The source factors over the fraction field and uses Gauss's lemma to
recover monic polynomial factors over the base. Here Mathlib's
unique-factorization instance for polynomial rings supplies an
irreducible factor directly over the smaller Tate algebra; the leading
coefficients normalize it to a monic prime factor. Noetherian
well-founded divisibility and the irreducible-implies-prime criterion
finish the proof without constructing a full factor list.

Source `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
The retained source is
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`,
“2. Affinoid algebras,” notes of part of Vladimir Berkovich's course.
The note-taker and publication date are unidentified.
