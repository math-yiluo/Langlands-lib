# Reduction of the local coroot component to coherent rank-one coordinates

`InducedCorootComponentProperty B hZ a` is the complete existential conclusion
of `KPLocalCorootComponentStatement` at one character. It asks for an affine
commutative group scheme, torus and induced-torus proofs, and a morphism into
the actual centralizer torus satisfying `CorootComponentCongruenceProperty`.
The latter definition retains the actual rational-point factorization, the
positive finite depth sum, and the inequality for every geometric character.

For a supplied `ValuedSL2RootCoordinates` record at a nonzero character,
`inducedCorootComponentProperty` takes the actual finite separable Weil
restriction of the multiplicative group as its source. Its representing
scheme is affine by construction. `WeilGm.isTorus_of_finite_separable` and
`WeilGm.isInducedTorus_of_finite_separable` supply the two torus properties.
The scheme morphism and character bound are exactly the ones proved in
`RankOneCorootGeometricCongruence`. The unitary namespace gives the same
conclusion for the ordinary character and its double, using the respective
ordinary and doubled congruence theorems.

`inducedCorootComponentProperty_of_valuedRankOneCoordinates` assumes explicit
providers of coherent records for every indivisible root of the supplied
building data. If its double is a root the provider gives unitary coordinates;
otherwise it gives special linear coordinates. These provider assumptions
are retained, rather than asserted to hold.

To treat any actual relative root `a`, the proof first uses
`IsSplitTorus.exists_pairing_eq_pos` to choose a cocharacter on which `a`
is positive. `IntegerValuationBuildingData.hasOppositeFactorPairs` supplies
actual opposite pairs without an additional building axiom. The theorem
`RelativeRoot.HasOppositeFactorPairs.exists_indivisiblePositiveRoot_eq_or_double`
then expresses `a` as an indivisible positive root `b` or its double. If the
double is a root, one supplied unitary record proves both alternatives. If
it is not, a supplied special linear record treats `a = b`, while the other
alternative contradicts the actual root membership of `a`.

All constructions work at arbitrary universe `u`, with the original local
field normalization and without a characteristic restriction. This internal
reduction uses the proved interfaces in `RankOneCorootGeometricCongruence`,
`WeilRestrictionInduced`, `PositiveRootConeDepth` and `IntegerRootReflections`.
It does not prove that the supplied coordinate providers exist, and therefore
does not establish the final unconditional `KPLocalCorootComponentStatement`.
