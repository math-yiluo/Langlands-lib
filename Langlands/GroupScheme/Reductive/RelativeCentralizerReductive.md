# Reductivity and maximal tori of actual relative cocharacter centralizers

This derived module proves that the specified actual relative cocharacter
centralizer in a reductive group over an arbitrary commutative ring is reductive.
The coefficient ring may be zero, disconnected, nonreduced or non-noetherian.
The cocharacter is given by a fixed integer vector in a supplied split torus.

`splitTorus.RelativeCocharacterCentralizer.isReductive` uses the actual affine
centralizer scheme and its actual inclusion. Smoothness and affineness are the
published arbitrary-base properties of this representative. On each geometric
fibre its base-changed inclusion represents the centralizer of the same integer
cocharacter in the actual reductive ambient fibre. The published field theorem
`dynamicCentralizerReductive` makes that actual fibre connected reductive and
therefore pseudo-reductive, supplying the required geometric-fibre clause.
`reductiveModel` packages this actual group with its reductivity certificate.

The auxiliary the existing `IsMaximalTorus.of_comp` proves that a torus which is maximal
in the ambient group remains maximal in a closed intermediate subgroup through
which its actual map factors. Closedness of the factored torus follows from its
closed composite. Any proposed larger closed torus in the intermediate subgroup
also gives a larger closed torus in the ambient group, so maximality applies.

`isFibrewiseMaximalTorus` applies this argument to the actual centralizer inclusion
on every residue-field fibre. Its specified factored torus map composes to the
original map after base change, retaining fibrewise maximality. The proof of this
maximality assertion uses the closed inclusion and original fibrewise maximality;
it does not use reductivity of the ambient group.

These facts support the centralizer and parabolic comparisons needed for Task
7200. They do not establish filtration overlap compatibility or effective descent.

The reductivity and fibrewise maximal-torus theorems are reused from
`LocalRankOneCentralizer`; closed-intermediate maximality uses
`IsMaximalTorus.of_comp` in `Torus.MaximalTransport`. This module retains the
reviewed `reductiveModel` construction on those same actual groups.
