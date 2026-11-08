# Renard VI.8.1 and VI.8.4: the aggregate statement

This module proves the unchanged `Statements` of
`Langlands.Representation.Families.RenardFamilyStatements`. The theorem
`Langlands.Renard.AlgebraicFamily.statements` keeps the published universe
parameters `uB, uG, uV, uE, uM`.

The source is Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026: VI.8.1, printed pp. 187–189 / PDF pp. 193–195, and VI.8.4
Theorem, printed p. 191 / PDF p. 197.
Literature ID: `renard-2026-representations-groupes-reductifs-padiques`;
SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Statement

`Statements.{uB, uG, uV, uE, uM}` is the conjunction, in this order, of

1. `FixedTensorComparisonStatement.{uB, uG, uV, uE}`, the fixed-tensor
   comparison used in the proof of the VI.8.1 Proposition;
2. `FlatnessCriterionStatement.{uB, uG, uV}`, the VI.8.1 Remark;
3. `AdmissibilityCriterionStatement.{uB, uG, uV}`, the VI.8.1 Proposition;
4. `SpecializationAdmissibilityStatement.{uB, uG, uV}`, the VI.8.1 Lemma;
5. `LocalFreeCoverStatement.{uB, uM}`, the VI.8.4 Theorem.

The aggregate adds no hypotheses and changes no conjunct.

## Proof

The proof is the anonymous constructor of the conjunction. Each component is
the theorem proving that conjunct at the same universes:

| Conjunct | Theorem | Module |
| --- | --- | --- |
| 1 | `fixedTensorComparison.{uB, uG, uV, uE}` | `Langlands.Representation.Families.RenardFamilyFixedTensorProof` |
| 2 | `flatnessCriterion.{uB, uG, uV}` | `Langlands.Representation.Families.RenardFamilyFlatnessProof` |
| 3 | `admissibilityCriterion.{uB, uG, uV}` | `Langlands.Representation.Families.RenardFamilyAdmissibilityProof` |
| 4 | `specializationAdmissibility.{uB, uG, uV}` | `Langlands.Representation.Families.RenardFamilySpecializationProof` |
| 5 | `localFreeCover.{uB, uM}` | `Langlands.Representation.Families.RenardLocalFreeCoverProof` |

The file imports the admissibility, specialization and local-free-cover proof
modules. The admissibility module imports the flatness module, which imports
the fixed-tensor module, so all five theorems are available. This module contains no
mathematical argument of its own. The arguments are in the paired Markdown
files of the five modules listed above.
