# Polynomial and analytic quotients by a Weierstrass polynomial

Author: Worker 56.

For any polynomial `w` over a nontrivial ultrametric normed commutative
ring `A`, `weierstrassQuotientMap w` is the algebra homomorphism from
`A[T]/(w)` to `A{T}/(w)` induced by polynomial inclusion. The map itself
needs neither completeness nor a monicity or norm hypothesis. When `w`
is monic and all its coefficients have norm at most one, it is injective;
when `A` is also complete, it is surjective and supplies
`weierstrassQuotientEquiv`.

To prove injectivity, suppose an ordinary polynomial is analytically
divisible by `w`. Compare this factorization with its ordinary polynomial
division. The proved norm estimate for analytic division forces the
polynomial remainder to have norm zero. Hence analytic divisibility is
equivalent to polynomial divisibility. Applying this equivalence to the
kernel of the displayed quotient map proves injectivity.

For surjectivity, choose an actual restricted-series representative and
divide it analytically by `w`. Its polynomial remainder represents the
same class. The resulting bijective algebra map supplies the displayed
algebra equivalence. No quotient equivalence is assumed, and the quotient
rings here require no topology or closedness assertion.

The quotient identification is property (2) of Definition 2.3.1,
page 5 of the retained Berkovich-course notes. Its analytic justification
comes from the Weierstrass division theorem on page 3; it also supplies
the principal-quotient case underlying the finiteness theorem,
Proposition 2.2.4 on page 4. At radius one, a monic polynomial with these
coefficient bounds is a Weierstrass polynomial in Definition 2.2.3,
page 4. The implemented norm estimate and division theorem establish
this quotient equivalence over the stated coefficient rings without
requiring multiplicativity of their norms.

Source `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
The retained source is
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`,
“2. Affinoid algebras,” notes of part of Vladimir Berkovich's course.
The note-taker and publication date are unidentified.
