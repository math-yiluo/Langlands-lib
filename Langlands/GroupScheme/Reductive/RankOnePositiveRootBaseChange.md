# Positive roots under field extension and the algebraically closed reduction

This is an internal consequence of the published actual split-torus root
support and lattice base-change comparisons. It retains arbitrary universe
`u`, every characteristic and every field extension `K/k` with both fields in
`Type u`. It introduces no external structural assertion or unconditional
rank-one proof.

For an affine group scheme `G` locally of finite type over `k`, a split
commutative torus `T`, and any actual homomorphism `i : T.toGrp ⟶ G`,
`positiveRootBaseChangeEquiv` identifies the characters that are actual roots
of `i` and positive on a specified cocharacter `ν` with the actual roots of
the pulled-back homomorphism positive on the pulled-back `ν`. Neither
reductivity, maximality nor a rank hypothesis is needed for this equivalence.
Its underlying function is the actual character pullback, as recorded by
`positiveRootBaseChangeEquiv_val`.

The construction restricts `characterLattice.baseChangeEquiv` to these
subtypes. Published `mem_roots_baseChange_iff` preserves and reflects root
membership, and `latticePairing_baseChange` preserves the integer pairing
exactly. Thus positivity is preserved and reflected, including in positive
characteristic; it is an inequality in `ℤ`, not in the ground field.

`linearIndependent_pair_baseChange_iff` proves that integral linear
independence of two characters is unchanged by pullback. The proof transports
the equation `m • α + n • β = 0` through the injective additive character
pullback and uses `LinearIndependent.pair_iff`. Consequently,
`roots_pairwise_dependent_baseChange_iff` preserves and reflects the
rank-one hypothesis in the exact target. Surjectivity of character pullback
and the root-membership comparison ensure that this statement covers every
root after extension.

`positiveRoot_uniqueness_baseChange_iff` proves that uniqueness of a root
positive on the specified `ν` is equivalent before and after extension. It
transports equality of the corresponding subtype elements through the
positive-root equivalence and its inverse. This includes empty positive-root
sets and the zero cocharacter.

`RankOneAlgClosedPositiveRootUniquenessStatement` is the exact public
`RankOnePositiveRootUniquenessStatement` restricted to algebraically closed
fields, with all other quantifiers and hypotheses unchanged. It is a
Prop-valued definition recording a proof obligation, not a proof.
`rankOneAlgClosedPositiveRootUniqueness_of_statement` restricts the full
statement to this case.

`rankOnePositiveRootUniqueness_of_algClosed` reduces the all-field target to
two explicit inputs: `MaximalTorusBaseChangeForwardStatement` and
`RankOneAlgClosedPositiveRootUniquenessStatement`. It pulls `G`, `T` and `i`
back to the chosen `AlgebraicClosure k`, which remains in `Type u`.
Published `IsConnectedReductive.baseChange_toAlgebraicClosure` supplies
connected reductivity, and published torus base change supplies splitness.
Maximality uses the first explicit input. The dependence comparison transports
the rank hypothesis, and the second input gives positive-root uniqueness on
the pulled-back cocharacter. The uniqueness comparison then reflects the
conclusion to `k`.

This reduction proves neither input. In particular, the published general
maximal-torus forward reduction retains structural premises, and the
algebraically closed geometric dimension argument remains open. Acceptance of
this helper does not prove properness of a dynamic quotient, a fixed-point
dimension bound, maximal-torus conjugacy or the exact parent target. It uses
none of the four theorem families excluded by the parent task.
