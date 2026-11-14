# Nearby root fixers along actual descended translation lines

This internal adapter specializes `NearbyRootFixer` to the supplied upper
apartment over the actual maximal unramified field. It introduces no new
building, integral model, valuation axiom, or fixed-point premise.

`KPApartmentData.descentTranslationMap` composes the existing linear
`descentCocharacterMap` with the quotient by the upper relative-root
annihilator. The two translation identities identify the existing
`descentTranslate` point with addition of this quotient vector, and identify
scalar multiplication of lower vectors with scalar multiplication of upper
translation vectors. The proof uses equality of apartment points through
their root-function families, followed by linearity.

For a nonarchimedean local field, connected reductive base group, maximal
split upper torus, and supplied upper apartment and centralizer satisfying
the full integer-valued V6 compatibility, `buildingDataOfApartment` packages
exactly these supplied data. The three eventual theorems apply the
integer-valued results of `NearbyRootFixer` to the quotient vector and rewrite
the translated point by the translation identities. They establish closed
facet incidence, simultaneous equality of every relative-root two-point
fixer with the translated singleton fixer, and equality of the corresponding
sharp fixers. The parameter tends to zero from both sides on each lower
torus direction.

Coefficient fixedness is unnecessary for these upper-apartment conclusions.
When the original point is fixed, the existing
`galois_fixed_descentTranslate` separately ensures fixedness of the
translated point. Neutral integral-point group comparisons and parabolic
special-fibre images require further integral-model arguments; this module
does not assert them.
