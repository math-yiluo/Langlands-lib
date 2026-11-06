# The represented-parabolic assembly for the lemma of Renard VI.7.1

Author: Worker 1777. This internal supporting result is the implication
`LeviCuspidalSupportAssociationReductionStatement`, implemented by
`leviCuspidalSupportAssociation_reduction`, in
`Langlands.Aubert.General.RepresentedParabolic`.

Its four antecedents are the existing global propositions
`RationalPointsFiniteLengthAdmissibleStatement`,
`ArbitraryParabolicJacquetAdmissibilityStatement`,
`RepresentedSupercuspidalSubquotientRealizationStatement`, and
`LeviSupercuspidalInductionAssociationStatement`.
All have independent universes `u, v`. Its conclusion is exactly
`LeviCuspidalSupportAssociationStatement` at those universes.
No antecedent is discharged. This conditional result does not prove
any of the host task's four unconditional targets.

The conclusion retains all the published field, topology, local compactness,
nonarchimedean group and connected reductivity hypotheses, both actual
rational parabolic triples and their matching rational Levi, geometric
unipotent radical and multiplication-isomorphism data. Each supercuspidality
condition still tests normalized Jacquet vanishing along every proper
actual rational parabolic of the corresponding Levi.
The result produces the target's actual `g`, group-scheme isomorphism
`φ` implementing conjugation by `g`, and equivariant linear equivalence
between the cuspidal representations.

The implemented argument starts from the given irreducible smooth `π`.
Irreducibility gives finite group-algebra length. The first antecedent
therefore gives its admissibility, and the second gives admissibility of
both normalized Jacquet modules on the literal Levi images.
The existing continuous multiplicative equivalences `leviPointsEquiv`
transport this admissibility to the Levi groups' own rational points,
with the canonical topologies used by the published functors.
The third antecedent then realizes each given supercuspidal subquotient
`ρᵢ` as a quotient of its Jacquet module.

Each quotient map is nonzero because its target is irreducible and hence
nontrivial. The inverse of the published actual Frobenius linear
equivalence sends it to a nonzero intertwiner from `π` into the induction
of `ρᵢ`. Irreducibility of `π` makes both intertwiners injective.

The target permits `π` in carrier universe `v`, whereas induction has
carrier universe `max u v`. To use the common-subquotient condition of
VI.5.4 without identifying universes, the proof takes the existing
`SmoothRep.universeLift.{u} π`. The existing actual equivariant
equivalence with `π` preserves irreducibility; composing its inverse
with each injection embeds this same lifted object in both inductions.
The published actual subrepresentation-to-subquotient result turns
these injections into subquotient witnesses. The fourth antecedent's
equivalence between its fourth and first conditions now gives exactly
the association required by the conclusion.

The provenance is internal: this is a composition of the four named
global propositions with the published actual Frobenius, transport,
irreducibility, universe-lift and subquotient APIs.
The motivating source is Renard 2026, VI.7.1 Lemma and proof,
printed p.180 / PDF p.186, read directly in the registered July 9, 2026
edition. The source also invokes VI.6.4 to describe the Jacquet
composition factors. The implemented implication starts with the
published target's actual subquotient witnesses and gets Jacquet
admissibility directly from admissibility of `π`, so it does not
need Jacquet finite length as an additional antecedent.
