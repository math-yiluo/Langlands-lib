# Local relative class formation

Worker 513 proves
`Langlands.ClassFieldTheory.Local.localRelativeClassFormation` with exactly the
published type
`Langlands.ClassFieldTheory.Local.LocalRelativeClassFormationStatement.{u}`,
for an arbitrary universe `u` and with no additional hypotheses. The statement
quantifies every prime `p` and concludes that one invariant family
`I : Langlands.ClassFieldTheory.Local.InvariantFamily.{u,u} p` satisfies all
nine finite relative properties.

The only published theorem used directly is
`Langlands.ClassFieldTheory.Local.localAbsoluteCorestrictionCompatibleClassFormation.{u}`
from module
`Langlands.ClassFieldTheory.Local.ClassFormationAbsoluteCorestrictionProof`.
For an arbitrary prime, the proof destructures that theorem's existential
witness and conjunction, then returns the same family with its
`ArithmeticNormalization`, `RelativeClassFormation`, `RelativeConjugacy`,
`RelativeCorestriction`, `FundamentalClasses`, `FundamentalInflation`,
`FundamentalRestriction`, `FundamentalCorestriction` and
`FundamentalConjugacy` proofs, in the target's order.

The discarded properties are `ContinuousInvariantProperties`,
`TateIsomorphisms`, `PositiveTateInflation`, `TateTransferCompatibility`,
`OrdinaryInflation` and `AbsoluteCorestriction`. The stronger proposition's
conjunct order and universe instantiation agree with the task description:
continuous properties occur immediately after arithmetic normalization, and
the other five additional properties follow fundamental conjugacy. No
transport of the witness or change of universe is needed.

This is a derived projection of the published simultaneous realization.
The original-source attribution is inherited from
[`ClassFormationStatement.md`](ClassFormationStatement.md): Jean-Pierre Serre,
*Local Fields* (1979), registered as `serre-1979-local-fields`, Chapter XIII,
§4, Theorem 1, printed pages 195–196, for local class formation, and Chapter XI,
§§2–3, printed pages 166–169, for its axioms and fundamental-class consequences.
The implemented proof uses the stronger Library theorem; its construction
and dependencies are documented in
[`ClassFormationAbsoluteCorestrictionProof.md`](ClassFormationAbsoluteCorestrictionProof.md).
