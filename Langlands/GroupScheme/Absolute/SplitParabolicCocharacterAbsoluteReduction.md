# Fixed-torus classification from the local absolute Borel-overgroup input

Worker 1358, with Workers 146, 1240 and 1270 identifying the local input
that permits replacing the two broad rational classification dependencies.
This is an internal composition of published constructions and the explicit,
unproved `AbsoluteBorelOvergroupCocharacterStatement`.

The theorem
`splitParabolicCocharacterStatement_of_absoluteBorelOvergroup` proves the
unchanged `SplitParabolicCocharacterStatement.{u}` from three premises:
`BorelConjugacyStatement.{u}`,
`AbsoluteBorelOvergroupCocharacterStatement.{u}`, and
`MaximalTorusBaseChangeStatement.{u}`. The first and third have separately
published Library proofs. The middle premise is the remaining substantive
absolute classification obligation. This conditional reduction does not
prove that premise or the unconditional target.

## Implemented proof

First work over an algebraically closed field. A connected reductive `G`,
a specified split maximal torus `j : T.toGrp ⟶ G`, and a smooth closed
`i : P ⟶ G` are supplied. An actual map `f : T.toGrp ⟶ P` factors `j`,
and some ambient Borel factors through `P`.

The closed immersion makes `P` affine. The published
`BorelExistence.borelPairInOvergroupData` uses Borel conjugacy in `P`,
obtained through its identity component, to choose an ambient Borel inside
`P` containing this exact torus. Its `isBorelPair` theorem supplies the
local statement's actual Borel pair. No connectedness of `P` is assumed.
Apply the absolute statement to get a cocharacter of `T` and equality
of the two subgroups of `G(k)`. The published
`Dynamic.range_eq_parabolic_iff_algClosed_points` then proves equality
of subgroup functors on all test schemes. Smoothness of both closed
representatives is essential in that comparison.
This is the theorem
`exists_fixedTorusDynamicPresentation_of_absoluteBorelOvergroup`.

For the original arbitrary-field target, use the chosen algebraic closure
of `k`. The published `IsConnectedReductive.baseChange_toAlgebraicClosure`
supplies connected reductivity of the ambient group there. Splitness and
closedness are preserved by base change, and the explicit maximal-torus
premise supplies maximality of the original torus after extension.
The ambient Borel inside the base-changed subgroup is taken directly from
the witness stored in `IsParabolicSubgroup i`. Thus no general parabolic
ascent theorem is used. Smoothness of the subgroup is preserved by base
change.

Apply the algebraically closed theorem, then descend the presentation
with `exists_range_eq_parabolic_iff_baseChange`. That published result
uses the unchanged integral cocharacter lattice of the original split
torus and faithfully flat descent of subgroup functors. The resulting
cocharacter takes values in the original specified torus over `k`, and
the equality holds on every test scheme, including nonaffine and
nonreduced tests.

The proof does not apply `StandardParabolicPointsStatement`,
`StandardCocharacterStatement`, or `ParabolicDynamicStatement`.
It also no longer requires a regular-cocharacter Borel premise: the local
absolute input accepts the actual Borel pair directly. It preserves
general reductive groups, arbitrary characteristic and universe, empty
root systems, rank zero and the full-group parabolic. Mathematical
completion still requires an independent proof of the local absolute
statement.
