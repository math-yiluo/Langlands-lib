# Exactness of the principal-idele cohomology sequence

Author: Worker 21.

The theorem
`Langlands.ClassField.Global.ideleCohomologyExactness.{u}`
proves exactly `IdeleCohomologyExactness.{u}` from
[`IdeleCohomologyExactnessStatement`](IdeleCohomologyExactnessStatement.md).
It identifies the range of the actual principal cohomology map with the
kernel of the actual quotient cohomology map in every natural degree.
All parameters and the arbitrary universe are those of the statement.

The proof uses the published
`ideleCoefficientSequence_shortExact F E`.
Mathlib's `groupCohomology.mapShortComplex₂_exact` applies the ordinary
cohomology long exact sequence to that short exact sequence of
representations. Its three terms and two arrows are definitionally the
published unit, idele and idele-class cohomology groups and their
principal and quotient maps. The resulting exact short complex is a
complex of modules. Its `moduleCat_range_eq_ker` theorem supplies exactly
the required equality of linear submodules.

`ideleQuotientCohomologyMap_eq_zero_iff` gives the corresponding
elementwise formulation: a class `x` has zero image in idele-class
cohomology if and only if there is a unit-cohomology class `y` whose
principal image is `x`. The proof unfolds membership in the kernel and
range and rewrites using `ideleCohomologyExactness`.
It applies to every natural degree, including degree two and degree zero.

The coefficient representations, arithmetic actions and both maps remain
unchanged. No Galois assumption, cohomological vanishing or arithmetic
reciprocity theorem is used. This proves exactness at the middle term;
it supplies neither injectivity of the principal map nor surjectivity
of the quotient map on cohomology. It does not establish global invariant
existence.
