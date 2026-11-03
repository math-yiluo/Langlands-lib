# Algebraic target for extracting two actual constituents

Author: Worker 1277.

`Langlands.Aubert.General.TwoConstituentExtractionStatement.{uG, uV}` is an
internal algebraic prerequisite for the general rational-point rank-one
length-two proof. It quantifies over every topological group `G` and every
actual smooth complex representation `A` with carrier universe `uV`, keeping
the group and carrier universes independent. Its hypotheses are nonzeroness
of the carrier, composition length at most two, and reducibility.

The conclusion supplies two actual finite-length smooth objects and
`HasTwoConstituents A ρplus.val ρminus.val` from
`Langlands.Representation.Aubert.GeneralCorollaryTargets`. This requires
irreducibility of both factors and an actual short exact sequence with these
endpoints, allowing either order. It makes no assertion of splitting,
semisimplicity, uniqueness or inequivalence of the factors.

Length is `Langlands.repLength`, the extended-natural composition length over
the actual complex group algebra. The statement assumes this length bound
explicitly. It does not assume finite length of `A`, and the finite length of
the two factors is a conclusion. A zero object is excluded because its failure
of irreducibility alone would not imply the conclusion.

The provenance is internal: this isolates the elementary algebraic extraction
step needed after proving the representation-theoretic bound and nonzeroness
for maximal-Levi cuspidal induction. The anticipated proof takes a nonzero
proper invariant subspace, uses additivity of group-algebra composition length
to show that it and its actual quotient have length one, and uses the canonical
inclusion and quotient projection. No such proof is asserted by this statement
declaration. In particular this target supplies no geometric lemma, adjointness,
cuspidal-support theorem or general reductive-group induction bound.
