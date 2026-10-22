# Norm bounds and primality of Weierstrass polynomial factors

Author: Worker 56.

The actual regrouping equivalence transfers Gauss norm multiplicativity
from the `(n+1)`-variable Tate algebra to restricted series over the
`n`-variable Tate algebra. Each monic polynomial has norm at least one,
because its leading coefficient is one. If the product of two monic
polynomials has all coefficients in the unit ball, multiplicativity
therefore bounds each factor's norm by one. The coefficient bounds follow
from the actual Gauss norm characterization.
These lemmas, including `monic_factors_coeff_le_one`, need an
ultrametric normed coefficient field but do not require its completeness.

The second result is independent of that specialized coefficient ring.
Over any nontrivial complete ultrametric normed commutative ring, a prime monic
unit-ball polynomial remains prime in the restricted-series algebra.
The previously constructed polynomial/analytic quotient equivalence
transfers the integral-domain property of its polynomial quotient to its
analytic quotient, which is equivalent to primality of the generated
principal ideal.

These implement the factor-closure and prime-transfer steps in the Rückert
argument of the retained Berkovich-course notes, Definition 2.3.1,
properties (1)-(2) on page 5 and Proposition 2.3.2(iii), pages 5-6.
The monic-factor observation also follows Definition 2.2.3 on page 4.
The norm proof is specialized to the actual Tate coefficient ring,
where multiplicativity has been proved; `prime_ofPolynomial` instead
uses the general algebraic quotient equivalence. Neither factoriality
nor integral closedness of the Tate algebra is assumed or concluded by
this module; these lemmas supply part of their later induction.

Source `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
The retained source is
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`,
“2. Affinoid algebras,” notes of part of Vladimir Berkovich's course.
The note-taker and publication date are unidentified.
