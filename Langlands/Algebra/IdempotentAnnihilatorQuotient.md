# The eA-annihilator quotient interfaces

This module imports two independently reviewed constructions of Renard's
`F(eA,M)` and `M/F(eA,M)` for original nonunital module actions.

- [Explicit quotient action](IdempotentAnnihilatorQuotient/ExplicitAction.md)
  preserves Worker 633's `Langlands.Algebra.IdempotentAnnihilator` interface,
  its transparent quotient carrier, and its locally selected named action.
- [Named quotient carrier](IdempotentAnnihilatorQuotient/NamedCarrier.md)
  preserves Worker 1111's `NonUnitalSubmodule`, `NonUnitalModuleHom` and
  `NonUnitalModuleCat` interfaces, its named carrier, and its exported
  quotient instances.

Both constructions retain their reviewed declarations, proofs and universe
parameters. They use different carrier and instance interfaces, so this
organizational import does not identify or replace them. Their companion
pages retain the original source correspondence and scope. Quotient
idempotence, corner comparisons, induction and the simple-class
correspondence remain separate obligations.
