# Pole presentations of composite and tensor operators

`RationalOperatorPolePresentation.comp` and `.tensor` apply the two
operations to the polynomial numerators and multiply the denominators.
The existing polynomial composition and tensor theorems give polynomiality
for each input, with a common scalar denominator chosen first. Bilinearity
preserves the cross-multiplication identities with the original operators.

`RationalUnitaryPoleFactorization.inversion` rewrites an inverted
basis-coordinate root power as the pullback of the corresponding Laurent
polynomial in the inverse coordinate, then uses the one-coordinate
factorization. Products stay factorable, and inversion preserves the
nonvanishing of the remainder on the unitary group.
`RationalOperatorPolePresentation.inversion` applies this to the denominator
and pulls back both polynomial numerators along character inversion.

`ActualCommonLeviV3.compactComparisonPolePresentation` takes pole
presentations for the actual forward operator and the actual forward
operator on the smooth dual. It tensors the first with the second at the
inverse parameter and multiplies by a cross-related presentation of the
inverse scalar. The published scalar-inverse identity identifies this
tensor with the actual common-Levi comparison on its genuine generic
locus after clearing denominators. Its cross identity with the original
presentation then follows from ambient density and polynomiality.

This is the algebraic assembly of the denominator in Waldspurger (2003),
IV.1(12) and V.3 formula (1), printed pp. 283 and 295 / PDF pp. 49 and 61
(`waldspurger-2003-plancherel`). The two operator pole presentations and
the cross-related scalar fraction are inputs to the construction.
