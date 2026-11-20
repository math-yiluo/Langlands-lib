# Henniart's candidate existence from the totally complex inputs

`Langlands.Henniart.candidateExistenceTCReduction` proves
`CandidateExistenceTCReductionStatement.{uK, uW, uP, uE, uQ}` at five
independent universe levels. The five hypotheses give a candidate at each
finite quotient of the absolute Galois group of a p-adic field, with the
automorphic lattice in universe `0`.
[Target statement](HenniartCandidateExistenceTCReductionStatement.md)

The proof applies `candidateExistenceTCReductionStatement_of_exactStabilizer`
to `candidateExistenceExactStabilizerTCReduction`. The first theorem adapts
the original Harris Proposition 4.8 hypothesis. An auxiliary character
with the exact Weil stabilizer in Harris's condition (4.12) satisfies
the general-position condition, so the given proposition applies to
that datum. The adapter passes the remaining four hypotheses to the
exact-stabilizer reduction at the same universes.
[Adapter](HenniartCandidateExistenceExactStabilizerReductionStatement.md),
[Harris implication](../Global/Arithmetic/HarrisProposition48ExactStabilizerStatement.md)

The second theorem is the published candidate construction over a totally
complex base. Its globalization retains `NumberField.IsTotallyComplex F`
for the common CM field `F` and uses the totally complex form of
Théorème 2.4 to construct the witnessed generators. The construction uses
the retained instance to apply the certified pole comparisons and the
composite-map hypothesis at `F`. It transports the resulting isometry to
the original local field, with the globalization's covering property
giving the required domain for the candidate.
[Candidate construction](HenniartCandidateExistenceExactStabilizerTCReductionProof.md),
[Totally complex globalization](../Global/Arithmetic/HenniartGlobalizationExactStabilizerTC.md)

This composition gives the reduction of Henniart (2000), Théorème 3.1
and §§3.7–3.8, under the five hypotheses in the target. The adaptation
of Harris (1998), Proposition 4.8, uses the stabilizer condition in the
proof of Lemma 4.7, p. 204.
[Registered originals](../../notes/henniart/sources.md)
