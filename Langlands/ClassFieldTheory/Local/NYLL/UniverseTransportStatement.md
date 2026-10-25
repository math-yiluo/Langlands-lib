# Universe transport targets for finite local reciprocity

This module defines three `Prop`-valued implication targets in
`Langlands.LocalClassField.NYLL`. It imports the published
[`TypeZeroStatement`](TypeZeroStatement.lean) aliases and reuses the host
[`FiniteReciprocityStatement`](../FiniteReciprocityStatement.lean) propositions.

In the following table, antecedent names belong to
`Langlands.LocalClassField.NYLL` and consequent names belong to
`Langlands.LocalClassField`.

| Declaration | Defining proposition |
| --- | --- |
| `FiniteAbelianReciprocityUniverseTransportStatement.{u, v}` | `FiniteAbelianReciprocityTypeZeroStatement → FiniteAbelianReciprocity.{u, v}` |
| `FiniteAbelianNormTransferUniverseTransportStatement.{u, v, w}` | `FiniteAbelianNormTransferTypeZeroStatement → FiniteAbelianNormTransfer.{u, v, w}` |
| `FiniteAbelianRestrictionUniverseTransportStatement.{u, v, w}` | `FiniteAbelianRestrictionTypeZeroStatement → FiniteAbelianRestriction.{u, v, w}` |

Each declaration has unapplied type `Prop` and no outer term parameters.
The reciprocity declaration has independent universe parameters `u`, `v`;
the other two have independent universe parameters `u`, `v`, `w`.
The corresponding field carriers in the consequents lie in `Type u`,
`Type v`, and, for towers, `Type w`. The antecedents have no universe
parameters: they are exactly the host propositions at `{0, 0}` or
`{0, 0, 0}`. No equality or ordering of universes is required.

## Preserved host content

Both sides of each implication use the existing propositions without
modification. Thus the consequent keeps every prime, field, algebra,
finite-dimension and scalar-tower hypothesis of its host declaration.
Reciprocity and norm-transfer retain arbitrary supplied `TF` and `TE`;
restriction retains arbitrary supplied `TF`. No canonical-data restriction
or additional comparison premise is introduced.

The host quotient groups still use the actual ranges of
`Units.map (Algebra.norm ...)`, with the supplied quotient topologies and
the actual Galois groups. Reciprocity retains its geometric normalization
through the inverse automorphism and its valuation-unit/inertia equivalence
for the same existential witness. Norm-transfer retains both distinct
directions: field norm corresponds to Galois inclusion, and scalar inclusion
corresponds, after Galois inclusion, to the degree power. Restriction retains
the normal-restriction equation. These facts follow directly from reusing
the host constants; their full formulations are documented in the
[host companion](../FiniteReciprocityStatement.md).

The only antecedent in each new proposition is the matching Type 0 target.
There is no transport certificate, chosen reciprocity map, extra reciprocity
assumption, or new model definition.

## Provenance and proof obligations

These are internal interface targets authored by Worker 100. Their provenance
is the displayed implication between published Library propositions, with
explicit universe instantiations. The interface follows unit 3(b) of the
[NYLL source audit](../../../../notes/reuse/nyll-finite-local-reciprocity-audit.md)
and the universe-transport boundary in section 7 of the
[port-feasibility report](../../../../notes/reuse/nyll-port-feasibility.md).
The implications are internal formalization goals; they are not attributed
as literal theorems of the external literature. This module copies no external
implementation and makes no claim of a new original-source verification.

The Lean file defines the propositions and supplies no proof of them or
axiom asserting them. A later implementation must construct any needed
coherent models and transport the same named Artin family. Those construction
requirements are stronger than these bare implications: the host propositions
make separate existential choices and do not identify witnesses across the
three statements or assert a globally coherent family. Stronger intermediate
targets and their proofs belong to the later transport proof unit.
The availability of `Shrink` helpers alone proves none of these implications.

The imported host and Type 0 pairs are unchanged. This module establishes no
reciprocity, uniqueness, class-formation, comparison with the cohomological
construction, or Weil-system theorem.
