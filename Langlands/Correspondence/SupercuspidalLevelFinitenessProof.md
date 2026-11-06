# Bounded-level supercuspidal finiteness reduction

Worker 357 proves the existing proposition
`Langlands.Henniart.SupercuspidalLevelFinitenessReductionStatement`
from `SupercuspidalFinitenessStatement.lean`, without changing its
definition or import closure. The field and representation-carrier
universes remain independent. The result covers every Mathlib
nonarchimedean local field with the field, valuation and topology
instances required by the published statement, and every positive rank.

The proof `supercuspidalLevelFinitenessReduction` takes the compact-open
finiteness assertion as its premise. For a field `F`, rank `n + 1`,
character `χ` of the actual group center and natural bound `b`,
`SupercuspidalClass.centralLevelStratum_eq` identifies the bounded-level
stratum with the fixed-vector stratum of
`Conductor.levelSubgroup F n b`. The published
`Conductor.levelOpenSubgroup F n b` has this underlying subgroup, and
`Conductor.isCompact_levelOpenSubgroup F n b` proves that it is compact.
Applying the premise to this actual compact open subgroup gives exactly
the desired finite set.

The helper `supercuspidalFiniteness_of_compactOpenFiniteness` packages the
same premise, its bounded-level consequence and the proved reduction into
the existing conjunction `SupercuspidalFinitenessStatement`.

This is an intrinsic proof of the published reduction, using the already
proved stratum identity and topology of the congruence subgroups. Its
source context is Bernstein--Zelevinsky (1976), Corollary 4.15, printed
page 41, for the still separate compact-open finiteness assertion, and
JPSS (1981), Section 5.1, printed page 211, for the last-row level
convention. The published statement and construction pairs retain the
source details. No additional source assertion is needed for this
reduction.

Compact-open finiteness remains a premise of both its bounded-level
consequence and the helper. This proof does not establish that premise,
finite-level existence, identification of the first fixed-vector level
with an epsilon exponent, numerical correspondence, local converse or
the closed supercuspidal correspondence theorem.
