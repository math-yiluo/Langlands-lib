# A geometric survivor count through parabolics with a fixed maximal Levi

This internal count applies to supplied represented geometric intersection
data for a finite family of pairwise nonconjugate target parabolics, all of
whose outer Levis are isomorphic to the source Levi. The source parabolic is
maximal proper. The supplied representatives enumerate the actual double
cosets. No geometric filtration is assumed or constructed by this count.

For every full-source index, full-intersection irreducibility infrastructure
shows that the target intersection Levi is full as well. The intersection
isomorphism therefore gives an isomorphism from the original source Levi to
the target Levi compatible with conjugation by the representative. Consequently
the conjugated target parabolic has the original embedded maximal Levi.

These conjugated parabolics have distinct subgroup images. Equality first
makes the two target parabolics rationally conjugate, so the separation
hypothesis identifies their family indices. The published self-normalizing
property of parabolics then identifies the double cosets of their conjugating
points, and the supplied enumeration identifies the remaining indices. All
multiplicities of the original geometric indices are retained.

`sum_fullSourceIndices_le_two_of_maximal` applies the actual-parabolic count
`maximalLeviParabolicCount_core` to this injective family. The resulting bound is
on the sum of all full-source cardinalities. The argument follows the
numerical idea of Renard VI.5.4 (printed pp.173–174 / PDF pp.179–180), using
parabolic images rather than a supplied finite Coxeter coordinate system.

A standard family supplies the separation premise through standard-parabolic
conjugacy rigidity. Constructing such a family, proving a geometric filtration,
and detecting every irreducible subquotient remain separate obligations.

With supplied geometric gluings and detection of every irreducible subquotient,
`hasRepresentedJacquetLengthWitness_of_separated_geometric_family` combines this
count with the published
`hasRepresentedJacquetLengthWitness_of_geometricBudget`. The theorem
`induced_repLength_le_two_of_separated_geometric_family` applies the published
exact detecting-family length bound. These two consequences retain independent
field and representation-carrier universes and the original canonical
topologies. They add no finite-length or Coxeter-coordinate premise, but the
supplied family, gluings and every-subquotient detection remain hypotheses.
They are conditional helpers and do not prove the host task's exact target.
