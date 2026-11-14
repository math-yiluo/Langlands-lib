# Positive-root fixer coordinates over any field

This internal support draft for Task 6309 extends the coordinate argument in the
published `ChamberPositiveCollection` and `PositiveRootFixerCoordinates` modules
to any field, connected reductive group, maximal split torus, and supplied
`KPApartmentData`. It adds no apartment axioms. It does not prove the zero/sharp
comparison or the final affine-root statement.

The first lemma derives the decomposition of every positive root into an
indivisible positive root or its double from the root-family ray property.
Positive integral descent supplies an indivisible root on the same ray; the ray
property leaves equality, doubling, or inverse doubling, and indivisibility
excludes the last possibility.

The ordered-product theorem repeats the published height-collection argument.
It enumerates each indivisible positive root and its double, omitting a double
that is not a root. Commutator height collects all factors in the specified
order. The doubled filtration is contained in the original filtration, so each
pair combines into the indivisible-root factor. This holds for zero-depth and
strict positive-depth groups at every point.

For a nonempty apartment subset, write an element of the intersection of the
positive depth-zero groups using the indivisible-root coordinates at one point.
Ordered root-point injectivity identifies these coordinates with the coordinates
at every other point. Each coordinate therefore lies in its root fixer over
the whole subset. The reverse inclusion follows from the root-fixer definition.

The final equality obtains the ray property and ordered coordinate injectivity
from actual rank-one factorization and opposite factor pairs, using the published
arbitrary-field results in `GenericPointSharpExchange` and
`ChamberIwahoriFactorPairReduction`. No boundedness, finiteness of the apartment
subset, local compactness, or unproved statement is assumed. The provenance is
the implemented proof of the three published modules just named, with the
affine-root-system premise replaced by its already proved rank-one consequence.
