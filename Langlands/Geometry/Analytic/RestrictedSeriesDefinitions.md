# Polynomial inclusion and distinguished restricted series

Author: Worker 56. The underlying restricted-series construction and
coefficient continuous linear map are imported from the Tate algebra
foundations authored by Worker 36 and generalized by Worker 56.

`RestrictedSeries.Algebra A` is the actual Tate algebra with the single
variable type `Unit`. `coeff A n` extracts its degree-`n` coefficient as a
continuous `A`-linear map. `ofPolynomial A` includes an ordinary polynomial
into this algebra. Its restriction condition is proved from the eventual
vanishing of polynomial coefficients, and its algebra-homomorphism laws
come from the ordinary polynomial-to-power-series map.

`IsNormalizedDistinguished f d` means that the degree-`d` coefficient is one,
all coefficient norms are at most one, and all coefficient norms strictly
above degree `d` are less than one. `IsDistinguished f d` means that the
degree-`d` coefficient is a unit, its norm bounds every coefficient norm,
and every coefficient above degree `d` has strictly smaller norm. Both
predicates are conditions on the constructed series alone. They contain
no division, factorization, or existence data.

The definitions require only an ultrametric normed commutative coefficient
ring. In the nontrivial case, a distinguished coefficient has positive
norm, so `d` is the last degree at which the coefficient norm attains its
maximum. For a norm-one ring, the normalized predicate is the
distinguished condition with leading coefficient one. These are
coefficient descriptions at radius one; neither predicate assumes a
multiplicative norm or completeness. The later division and preparation
statements supply their own needed hypotheses.

The source is Section 2.2, pages 2–3, of the retained fourteen-page notes of
part of Vladimir Berkovich's course, “2. Affinoid algebras.” Page 2 defines
the restricted-series Banach ring; page 3 defines its order and
distinguished elements. This is a derived presentation: the source uses a
complete, multiplicatively normed ring and arbitrary positive radius.
The Lean definitions specialize the radius to one, express the last
maximal coefficient directly, and retain the same coefficient conditions
under weaker ambient hypotheses. The normalized predicate is the internal
form used after dividing by the distinguished coefficient.

Registered source:
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
PDF SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`,
retained at
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`.
The note-taker and publication date are unidentified.
