# The represented-parabolic assembly for Renard VI.7.1

Author: Worker 1777. This internal supporting result is the implication
`LeviCuspidalSupportSurjectiveReductionStatement`, implemented by
`leviCuspidalSupportSurjective_reduction`, in
`Langlands.Aubert.General.RepresentedParabolic`.

Its four antecedents are the existing global propositions
`LeviInductionFiniteLengthStatement`,
`RationalPointsFiniteLengthAdmissibleStatement`,
`ArbitraryParabolicJacquetAdmissibilityStatement`, and
`RepresentedSupercuspidalSubquotientRealizationStatement`.
All have the independent universes `u, v`. The conclusion is precisely
`LeviCuspidalSupportSurjectiveStatement` at those universes. No antecedent
is discharged, and this conditional result does not complete any of the
four unconditional targets of the host task.

The conclusion retains every field, topology, local compactness,
nonarchimedean group and connected reductivity hypothesis of the published
target, along with every actual rational parabolic, rational Levi,
matching geometric unipotent radical and multiplication isomorphism.
Supercuspidality is the target's written-out vanishing condition for every
proper actual rational parabolic of the Levi group.

For an irreducible supercuspidal representation `ρ` of the Levi, its
group-algebra module is simple and hence has finite length. The first
antecedent gives finite length of its actual normalized induction `I`.
The published continuity of the actual Levi projection, together with
the published nonvanishing theorem for normalized induction, makes `I`
nonzero. The published finite-length comparison and irreducible-existence
theorem then give an irreducible subrepresentation `π` of `I`.
The published actual Frobenius linear equivalence carries the nonzero
inclusion to a nonzero intertwiner from the normalized Jacquet module
of `π` to `ρ`. Irreducibility of `ρ` makes it surjective.

For the finite-family clause, apply the independent-universe theorem
`SmoothRep.finiteLengthIrreducibleSources` to `I`, choosing source carrier
universe `v` while `I` has carrier universe `max u v`. Its finite list
therefore lies in exactly the universe required by the target.
For any small irreducible `π` in question, its automatic finite length
and the second antecedent give admissibility. The third antecedent
gives admissibility of its normalized Jacquet module on the literal
Levi image. Transport along `leviPointsEquiv` supplies admissibility on
the Levi's own rational points, with its canonical topology.
The fourth antecedent realizes the supercuspidal subquotient `ρ` as
a quotient. Its surjective map is nonzero; inverse Frobenius supplies
a nonzero map from `π` to `I`. The chosen finite list catches `π` up
to categorical isomorphism.

The provenance is internal: this is a composition of the four named
propositions with the published actual functors, transport,
irreducibility and finite-length APIs. The motivating source is
Renard 2026, VI.7.1 Proposition and proof, printed p.180 / PDF p.186,
read directly in the registered July 9, 2026 edition. The implementation
follows its two Hom-space arguments and makes the carrier-universe
distinction explicit. It retains the published target's fixed-parabolic
scope and asserts no additional result about the full map on cuspidal
association classes.
