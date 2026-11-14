# Relative Borels from cocharacters with a maximal-torus centralizer

This internal adapter supplies the negative Borel clause in the local
opposite-Borel construction. It assumes a reductive group scheme over an
arbitrary scheme, a supplied split torus with a closed fibrewise maximal
inclusion, and a cocharacter whose whole dynamic centralizer equals the
range of that inclusion on all test schemes.

`isRelativeBorelSubgroup_of_torusCentralizer` proves that every monomorphic
representative of the cocharacter's dynamic parabolic is a relative Borel.
The supplied representative is closed because the published dynamic
representability theorem gives a closed representative of the same
subgroup functor, and the two representatives are isomorphic compatibly
with their inclusions. The published dynamic smoothness theorem gives
smoothness over the original base.

For a field-valued point, the proof pulls back the torus, cocharacter and
both subgroup representations. Reductivity and torus maximality apply to
that actual field fibre. The published
`isRegularCocharacter_of_centralizer_isRepresentedBy_torus` gives root
regularity from the centralizer representation, and the first clause of
`regularCocharacterBorel` proves that the pulled-back representative is
Borel. To obtain the geometric Borel condition on a residue fibre, the
proof applies this argument at its algebraic-closure-valued point and
uses the canonical pullback comparison and its naturality to identify
the resulting inclusion with the iterated residue-field pullback.
The published geometric Borel descent theorem then also supplies the
Borel property over the residue field itself.

`isRelativeBorelSubgroup_opposite_of_torusCentralizer` applies this result
to the negative lattice cocharacter. Negation is inversion of the
multiplicative-group parameter, which preserves the dynamic centralizer.
No positive Borel or positive parabolic presentation is needed.

`RelativeLevi.DynamicBorelData χ` records an actual group scheme and its
closed relative Borel inclusion whose all-test range is `Dynamic.parabolic χ`.
`oppositeBorelOfTorusCentralizer` constructs such data for the opposite
cocharacter. It selects a closed representative from
`dynamicBaseRepresentability` and proves that the selected representative
is Borel by the preceding adapter. Its output supplies the group,
inclusion, closedness, relative Borel property and all-test range equality.
`exists_oppositeBorel_of_torusCentralizer` exposes these certificates as an
existential statement for local-presentation consumers.

These are internal deductions from published Library results about
dynamic representability, smoothness, root regularity and field Borels.
They assume the centralizer equality and do not construct its
cocharacter, establish local presentations or prove the full opposite
Borel statement.
