# Specialization of supplied algebraic rank-one coordinates

The definitions `ValuedSL2RootCoordinates.ofAlgebraic` and
`ValuedSU3RootCoordinates.ofAlgebraic` turn supplied coherent algebraic coordinates
into the exact published valued coordinate records over `K = UnramifiedClosure F`.
They retain the field or quadratic tower, both coordinate equivalences, the rank-one
homomorphism and the induced-torus coroot morphism unchanged. They require a relative
root and an actual normalizer image of the standard Weyl element; the SU3 constructor
also requires that the double be a root. These constructors assert no algebraic
coordinate existence and add no residual-characteristic restriction.

The origin is the midpoint constructed in `ValuedRankOneCoordinateAssembly` or
`ValuedSU3CoordinateAssembly`. The chosen henselian separable extension valuation
is norm-calibrated by
`IntegerValuation.isNormCalibrated_henselianSeparableAddValuation`. In the unitary
case it is invariant under quadratic conjugation by
`SU3Root.henselianSeparableAddValuation_quadratic_bar`. The generic coordinate-depth
theorems then give both SL2 formulas or all four SU3 formulas. The latter specialize
definitionally to `SU3Root.towerDepth` and `SU3Root.towerCentralDepth`, normalized on
`K`. Full centralizer compatibility and the reductive/maximal-split hypotheses come
from the supplied building record.

This is internal derived packaging of those proved comparison theorems and the
published valued record definitions. Algebraic coordinate existence remains a
separate prerequisite for the unconditional target statement.
