# Lifted rank-one character for the extension construction

Author: Worker 469.

`Langlands.RankinSelberg.rankOneExtensionCharacter` names the exact scalar
representation used in the published `RankOneExtensionLDivisibilityStatement`.
For a canonical p-adic field and a bundled continuous complex quasicharacter,
it conjugates the existing scalar `rankOneCharacter` through
`ULift.moduleEquiv.symm`. Its carrier is `ULift.{uW} Complex`, independently
of the field universe `uF`. Unfolding the abbreviation gives precisely
the conjugated monoid action in that target. The target itself and its
imports are unchanged.

`rankOneExtensionCharacter_isOfWhittakerType` proves the entire existing
`IsOfWhittakerType` predicate for this action and the standard rank-one
character of the supplied unitary additive character. The proof applies the
published `rankOneWhittakerType` to the scalar representation, then transports
its certificate using `IsOfWhittakerType.of_equiv`. The underlying linear
equivalence is `ULift.moduleEquiv.symm`; its compatibility with the conjugated
action is definitional. Thus admissibility, finite generation over the actual
group algebra, and the linear equivalence of the whole Whittaker-functional
space with the complex scalars all transport together. The separate
`rankOneExtensionCharacter_isSmooth` extracts smoothness from admissibility.
Both lemmas retain the supplied additive character. No extra scalar-type or
smoothness premise is assumed.

This is an internal derivation from the published scalar theorem and
representation-equivalence API. It introduces no independent literature
result. Continuity of the quasicharacter and continuity, unitarity and
nontriviality of the additive character remain in their existing bundles.
There is no restriction on field or carrier universes. This unit constructs
neither an induced Whittaker functional nor a pair polynomial; the compact
section, Fourier smoothing, analytic comparison and final divisibility
obligations remain separate.
