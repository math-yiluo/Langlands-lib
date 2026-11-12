# Renard VI.8.2 and VI.8.3: the conjunction

Author: Worker 5188. This module proves the unchanged `ParabolicStatements` of
[RenardFamilyParabolicStatements](RenardFamilyParabolicStatements.md). The theorem
`Langlands.Renard.AlgebraicFamily.parabolicStatements` keeps the published
universe parameters `u, uB, uC, uE, uV`.

The source is Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026: VI.8.2 Proposition and formula (VI.8.2.2), printed p. 190 /
PDF p. 196, and VI.8.3 Proposition, printed p. 191 / PDF p. 197.
Literature ID: `renard-2026-representations-groupes-reductifs-padiques`;
SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Statement

`ParabolicStatements.{u, uB, uC, uE, uV}` is the conjunction, in this order, of

1. `InductionBaseChangeStatement.{u, uB, uC, uE}`, the VI.8.2 Proposition
   (base change commutes with induction);
2. `JacquetFiniteTypeStatement.{u, uB, uV}`, the VI.8.3 Proposition (Jacquet
   modules preserve finite generation).

The conjunction adds no hypotheses and changes no conjunct.

## Proof

The proof is the anonymous constructor of the conjunction. Each component is
the theorem proving that conjunct at the same universes:

| Conjunct | Theorem | Module |
| --- | --- | --- |
| 1 | `inductionBaseChange.{u, uB, uC, uE}` | `Langlands.Representation.Families.RenardFamilyInductionBaseChangeProof` |
| 2 | `jacquetFiniteType.{u, uB, uV}` | `Langlands.Representation.Families.RenardFamilyJacquetFiniteTypeProof` |

This module contains no mathematical argument of its own. The arguments are in
the paired Markdown files of the two modules listed above.
