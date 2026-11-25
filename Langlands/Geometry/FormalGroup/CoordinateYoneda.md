# Formal coordinate maps from natural nilpotent-point maps

This internal reconstruction works over an
arbitrary commutative ring R with finite source and target coordinate
types. Test algebras are all commutative R-algebras in the universe of
R.

`IsNaturalPointMap` requires a family of maps between actual nilpotent
tuples to commute with every coefficient-algebra homomorphism.
Evaluation of every actual coordinate map has this property.
`CoordinateMap.ext_of_eval` proves that equal evaluation on all such
tuples determines the coordinate map: evaluate on a sufficiently large
universal truncated polynomial point and extract the desired
coefficient.

For a given natural family, evaluate at each universal box point and
choose polynomial representatives of the resulting quotient
coordinates. Naturality under box quotient maps proves that the
coefficients of these representatives agree wherever both are
defined. `seriesOf` assembles those compatible coefficients into an
actual multivariate power series. Evaluation at the m = 1 box point
shows that its constant coefficients vanish when the family preserves
zero.

`CoordinateMap.ofNatural` is the resulting pointed formal coordinate
map. Its evaluation agrees with the original family on every actual
nilpotent tuple, since every such tuple comes from a universal box
point and a sufficiently large box computes its evaluation.

No additivity is required in this file. Formal group homomorphism and
scalar-commutation properties are recovered separately from the
corresponding properties of the family. This is internal infrastructure
for the actual inverse-numerator construction, rather than a quotation
of external literature.
