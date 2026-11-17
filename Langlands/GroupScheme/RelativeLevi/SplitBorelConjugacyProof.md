# Zariski-local conjugacy of Borel subgroups of a split reductive group

Worker 670, with Worker 696's local normalizer-conjugacy reduction.

`Langlands.GroupScheme.splitBorelZariskiLocalConjugacy` proves exactly
`Langlands.GroupScheme.SplitBorelZariskiLocalConjugacyStatement.{u}`.
It applies to every universe and every commutative ring with the reductivity,
closed coordinate split torus, fibrewise maximality, common fibrewise root
datum and free rank-one root-weight hypotheses of that published statement.

The proof applies
`splitBorelZariskiLocalConjugacy_of_structure_and_lifting` to the two
unconditional Library theorems `splitBorelVectorSeries` and
`splitNormalizerGeometricLocalLifting`, all in the same universe.
The former supplies a relative Borel containing the specified torus,
its split torus quotient and an actual affine kernel with a finite affine
vector-quotient series. The containment part of the reduction uses local
cocycle trivialization and descent to obtain an open neighbourhood of each
base point and an actual rational conjugator for any given relative Borel.
The resulting containment is an inclusion of subgroup functors on every
scheme test over that open.

For two relative Borels containing the specified torus, the other part of
the reduction uses the geometric normalizer-lifting theorem and the
published parabolic containment and spreading results. It obtains an
actual rational point in the full normalizer of the pulled-back torus,
conjugating the first Borel range onto the second on every scheme test.
Together these are precisely the two conjuncts of the target.

This is an internal derived proof by composition of the three indicated
Library theorems. It introduces no further mathematical hypotheses; the
published target and all its imported definitions are used unchanged.
The arbitrary-ring scope includes disconnected and nonreduced bases.
For the zero ring, the target's assertions around a base point are vacuous.
