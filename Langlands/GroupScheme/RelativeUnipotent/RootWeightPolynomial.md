# Actual homogeneous polynomial coordinates on root charts

This derived module places the actual root-chart group law in the Library's
corepresented homogeneous-coordinate language over an arbitrary commutative base
ring. It uses the actual torus action constructed in `RootWeightTorusAction`.

`AutomorphicAction.affineTorusAction` reads any actual split-torus automorphic
action on the group's affine-point functor, naturally for every coefficient
algebra. The construction does not require a field.

`RootHeightChart.polynomialCorepresentation` corepresents the actual affine-point
functor of the chart group by its original multivariable polynomial ring. It uses
`AffineLinearEmbedding.corepresentableBy` with the scheme chart, so the group law
is the original group's law; the chart is not asserted to be additive.
`polynomialTorusAction` is the actual conjugation action on that functor.

`polynomialCoordinate_sections` identifies algebra coordinates with the original
ordered root coordinates using the relative spectrum/global-sections comparison.
`isHomogeneous_polynomialVariable` proves that every polynomial variable is
homogeneous of precisely its ambient root character. The proof applies the
arbitrary-ring homogeneous/eigenfunction criterion to the actual coordinate
scaling theorem, and uses the affine section comparison to evaluate root
characters in the coefficient algebra. Nilpotents in that algebra are allowed.

These are coordinates on the full supplied root-height chart. Restriction to a
cocharacter and identification of secondary root-weight cutoffs with intrinsic
cyclic weight subgroups remain separate constructions; this module makes no
claim about changes of maximal torus or descent.
