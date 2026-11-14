# Actual simple-coroot coordinates on a pinned torus

This internal construction applies to a supplied split pinning whose integral
coroot span is the full cocharacter lattice. The existing
`Langlands.RootDatum.simpleCorootBasis` and its dual fundamental-weight basis
then supply coordinates on the actual torus, including the empty basis.

`simpleCorootPoint` evaluates an actual simple coroot at a field unit.
`fundamentalWeightEval` evaluates the dual character. Their pairing is the
Kronecker pairing. Therefore the commutative product of the simple-coroot
points has precisely the prescribed coordinates.

The proof that coordinates separate points first extends equality from the
fundamental-weight basis to all characters. It then uses the published
character evaluation equivalence for a split torus.
`simpleCorootCoordinates` is the resulting multiplicative equivalence
between actual rational torus points and unit tuples. The inverse is the
product of the evaluated simple coroots.

Finally, `simpleCorootSpan_eq_top` discharges the lattice hypothesis for an
algebraically simply connected group using the published necessity theorem.
This construction is derived from the Library's integral coroot and
character-evaluation results; it adds no root-generation assertion.
