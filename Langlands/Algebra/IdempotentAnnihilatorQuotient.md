# The eA-annihilator quotient interfaces

This module imports two constructions of Renard's
`F(eA,M)` and `M/F(eA,M)` for original nonunital module actions.

- [Explicit quotient action](IdempotentAnnihilatorQuotient/ExplicitAction.md)
  preserves the `Langlands.Algebra.IdempotentAnnihilator` interface,
  its transparent quotient carrier, and its locally selected named action.
- [Named quotient carrier](IdempotentAnnihilatorQuotient/NamedCarrier.md)
  preserves the `NonUnitalSubmodule`, `NonUnitalModuleHom` and
  `NonUnitalModuleCat` interfaces, its named carrier, and its exported
  quotient instances.

Both constructions retain their declarations, proofs and universe
parameters. They use different carrier and instance interfaces, so this
organizational import does not identify or replace them. Their companion
pages retain the original source correspondence and scope. Quotient
idempotence, corner comparisons, induction and the simple-class
correspondence are in separate modules: `IdempotentAnnihilatorComparisons`,
`NonUnitalModuleCornerInduction` and `NonUnitalModuleCornerSimpleStatements`
with its proof `NonUnitalModuleCornerSimpleProof`.
