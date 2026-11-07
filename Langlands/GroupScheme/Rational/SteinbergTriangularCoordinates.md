# Actual unit diagonal and Steinberg character triangularity

Authors: Worker 1284 and Worker 1317. This is an internal assembly of the
published actual coefficient calculation and arbitrary-field local
nonvanishing proof. It introduces no additional mathematical premise.

`fundamentalTraceDiagonalUnit e x s F i` is the actual coefficient of the
own-variable monomial in the restriction of the supplied fundamental trace
character, regarded as a unit of the coefficient field. Its value is precisely
`fundamentalTraceDiagonal e x s F i`; no scalar-one normalization is asserted.
The construction is over algebraically closed fields in arbitrary universe
`u` and arbitrary characteristic, with an actual affine group, supplied split
pinning, ordering, normalized root maps, reflection representatives and
fundamental-representation family. The family remains supplied data.

The proof first uses the private helper
`simpleRootHighestCoefficientNonvanishingForTriangularity` to specialize
`NormalizedRootParametrization.coefficientMatrix_one_reflected_ne_zero` from
`SimpleRootHighestCoefficientNonvanishing` to the published algebraically
closed local proposition. Every representation, highest-weight package,
pairing-one simple root, supplied root map and representative, and nonzero
highest vector is retained. The helper exports no public declaration and thus
does not conflict with the separate exact local proof module. Applying the published
`fundamentalTraceDiagonal_ne_zero_of_simpleRootHighestCoefficient` then proves
that each actual diagonal coefficient is nonzero. `Units.mk0` turns this
coefficient into the displayed unit.

`steinbergRestriction_fundamentalCharacter` states the actual coordinate
identity with these units and the previously defined
`fundamentalTraceRemainder`. It follows by unfolding the remainder and the
unit's value. The previously proved lower-remainder theorem uses strict
increase in the canonical squared length of the fundamental highest weights;
its relation is well founded. The existing diagonal-nonvanishing assembly
therefore gives `hasTriangularFundamentalRestriction` without a local
nonvanishing premise.

Finally, `splitSteinbergCharacterTriangular` has exactly the published
`SplitSteinbergCharacterTriangularStatement.{u}` as its type. It applies the
existing conditional triangularity theorem to the now proved local
proposition. In particular it retains every supplied ordering, root map and
reflection representative, including the empty family. It uses no factorial
division, rational-point density or restriction on the characteristic.

This unit proves triangularity for supplied fundamental representations. It
does not construct those representations, prove simple-connectedness ascent,
or prove the final arbitrary-field `SplitSteinbergQuotientStatement`. Those
remaining assembly inputs are separate obligations.
