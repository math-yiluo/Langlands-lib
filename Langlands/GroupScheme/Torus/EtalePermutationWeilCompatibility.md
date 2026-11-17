# Actual Weil charts with the original local permutations

This derived module constructs actual split charts of the Weil group of the
invariant coefficient algebra and proves that they satisfy exactly the same
local permutations as the supplied torus charts. It assumes an affine base and
a finite flat jointly surjective affine chart family, with varying finite
coordinate types. Empty coordinate types and zero rings are allowed.

A coefficient datum describing one constant permutation on all unit tests has
that coefficient reindexing map. The original chart agreement supplies this
unit formula on its common base. Thus the actual overlap coefficient equivalence
restricts to the original local permutation. Coefficient naturality and the
invariant-overlap equation give `invariant_local_permutation`: every invariant
coefficient has the same local permutation of chart values.

`chartTensorEquiv` extends the actual local coefficient splitting to every
relative test using the structure map's action on global sections. Its pure
tensor formula is the restriction of the invariant coefficient multiplied by
the test section. This equivalence is natural for all relative test morphisms.
Composing it with the natural raw-section Weil point model constructs
`coordinateWeilChart` as an actual group-scheme isomorphism, via the published
representable point-model construction.

`chartTensorAlong` expresses both chart evaluations using one specified common
test base, and `coordinateWeilChart_coordinates` identifies it with the original
Weil-group coordinates. Tensor induction extends the invariant coefficient
permutation identity to every tensor. Passing to tensor units proves
`weil_agreeBy_of_original`: on each original overlap open, the actual Weil charts
satisfy the same coordinate permutation on every relative test. No choice of a
new open or a new permutation is needed.

This proof is internal and derived from the coefficient descent, local splitting,
and representable point-model constructions imported by the Lean file. It does
not yet glue the local comparisons into a global group-scheme isomorphism or
assert the unchanged relative-Borel presentation statement.
