# Proof of structural unramified root specialization

Lean module: `Langlands.Geometry.Building.UnramifiedRootSpecializationProof`.

The theorem `Langlands.Geometry.Building.unramifiedRootSpecialization` proves
the published statement
[UnramifiedRootSpecializationStatement](UnramifiedRootSpecializationStatement.md),
and its type is exactly `UnramifiedRootSpecializationStatement.{u}`. The
universe is arbitrary. The proof adds no premise, no unproved proposition and
no new axiom.

## Proof

The proof is a single term. It combines two published Library theorems:

- `unramifiedRootSpecialization_of_fixedResidueRootModel` from
  [UnramifiedRootSpecializationReduction](UnramifiedRootSpecializationReduction.md).
  It proves
  `UnramifiedFixedResidueRootModelStatement.{u} → UnramifiedRootSpecializationStatement.{u}`.
  For a Galois-fixed upper point, it takes the fixed-point model, its closed
  split integral torus and the reductive quotient of its special fibre. The
  specialization data come from the construction
  `IntegralTorusData.rootSpecializationData`, and reduction compatibility
  follows from the integral and positive root-point identities.
- `unramifiedFixedResidueRootModel` from
  [UnramifiedFixedResidueRootModelProof](UnramifiedFixedResidueRootModelProof.md).
  It proves the hypothesis
  [UnramifiedFixedResidueRootModelStatement](UnramifiedFixedResidueRootModelStatement.md)
  at the same universe.

Applying the first theorem to the second gives the target. This module has no
other content.

## Provenance

This is an internal deduction from the two Library theorems named above. It
makes no literature claim beyond the claims recorded in the statements and
proofs it combines. Their Markdown cites, among other results, Kaletha and
Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Propositions 9.4.23,
9.4.25 and 9.4.28.
