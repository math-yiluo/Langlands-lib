# Vanishing coinvariants along a finite filtration

Author: Worker 168. `Langlands.Jacquet.CoinvariantFiltrationVanishingTheorem`
is an internal algebraic prerequisite for quasicuspidality of the associated
Jacquet filtration. It states a property of the published actual
`ObjectRepFiltration`, its `gradedRepresentation` quotients, and the actual
subgroup coinvariant quotient `Jacquet.Coinvariants`.

For every commutative ring, group, representation, finite filtration and subgroup,
if every graded quotient has zero subgroup coinvariants, the ambient
representation also has zero subgroup coinvariants. Coefficients, group and
carrier have independent universes. The subgroup need not be normal. The
statement permits zero representations, zero graded factors, and a filtration
of length zero. It assumes no topology, smoothness, admissibility, finite
dimension, finite module length, irreducibility, or splitting.

The provenance is elementary quotient algebra, rather than a transcription
of a source theorem. The intended proof restricts the ambient coinvariant
projection to each filtration step. Inductively it kills the preceding step,
so it factors through the actual graded quotient. That map is invariant under
the subgroup, hence factors through the graded quotient's zero coinvariants.
Thus the ambient projection vanishes on the next step, and finally on the whole
representation. This paragraph explains the mathematical rationale; this module
only states the proposition and does not supply its proof.

Applying the statement separately to each proper block refinement's unipotent
radical gives closure of `IsLeviQuasicuspidal` under finite actual filtrations.
That application and the geometric lemma are separate proof obligations.
