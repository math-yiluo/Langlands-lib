# Characteristic powers in torus-equivariant additive polynomials

This internal derived construction supplies the polynomial step in the comparison
of roots under an actual reductive isogeny. It does not prove existence of a root
image, a root-index bijection, centrality, or the complete root-datum statement.

The input is a nonzero additive polynomial over an arbitrary field, a specified
split torus, and two actual torus characters. Equivariance is an equality of
polynomials over the torus's actual coordinate algebra, obtained by evaluating
characters at its universal point. This retains nonreduced algebra tests and does
not restrict equivariance to rational points. If the source character is nonzero,
`powerMonomial` supplies a nonzero field scalar and a natural number `r` such that
the polynomial is that scalar times `X^(ringExpChar k ^ r)` and the target
character is `ringExpChar k ^ r` times the source character.

The proof first uses the published binomial coefficient relations for additive
polynomials. In characteristic zero the relation with binomial index one forces
every nonzero coefficient to have degree one. In positive characteristic the
published additive-polynomial support theorem gives a prime-power degree.
Comparing coefficients in the universal equivariance equation identifies each
nonzero coefficient's degree multiple with the target character. Multiples of a
nonzero character of a split torus are distinct, as follows from the published
injection into its rationalized character lattice. Thus only one coefficient is
nonzero. The scalar and exponent are packaged with both equations.

Provenance: derived from the Library's actual character-unit embedding,
`TorusLinearization.IsAddPoly₁.choose_mul_coeff`, its positive-characteristic
support theorem, and `IsSplitTorus.character_toRat_injective`. No additional
mathematical assertion is assumed.
