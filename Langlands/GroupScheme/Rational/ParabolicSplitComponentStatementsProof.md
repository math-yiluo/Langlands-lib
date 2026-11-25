# Split components of parabolic subgroups (Renard V.3.1–V.3.2): the assembled statement

Module `Langlands.GroupScheme.Rational.ParabolicSplitComponentStatementsProof`, namespace
`Langlands.GroupScheme`, universe parameter `u` (the universe of the base field).

## What is proved

The theorem `Langlands.GroupScheme.parabolicSplitComponents` has exactly the type
`ParabolicSplitComponentStatements.{u}`. That is the published conjunction in
[ParabolicSplitComponentStatements](ParabolicSplitComponentStatements.md):

`ParabolicSplitComponentLeviStatement.{u} ∧ LeviSplitComponentRadicalStatement.{u} ∧
ParabolicSplitComponentConjugacyStatement.{u} ∧ LeviCentralizerCharacterizationStatement.{u} ∧
MinimalParabolicSplitComponentStatement.{u}`.

These five statements formalize the split-component assertions of Renard V.3.1 and the first
sentence of V.3.2 (David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`;
V.3.1–V.3.2 on printed p.110 / PDF p.116). The theorem asserts nothing beyond the conjunction.
The qualifications recorded in the statement Markdown therefore apply unchanged:

- the statements hold over an arbitrary field `k`, while Renard's `F` is a nonarchimedean local
  field;
- the radical `r : R ⟶ P` and the unipotent radical `u : U ⟶ P` of the parabolic are supplied
  as hypotheses, and their existence is not asserted;
- a split component of `P` is, following V.2.1 literally, a maximal split torus
  `a : A ⟶ R` of the supplied radical;
- `Z(G, A)` is the centralizer subgroup functor `torusCentralizer`, and "`M` is `Z(G, A)`"
  means representation of that functor by the given monomorphism (`IsRepresentedBy`);
- the conjugacy statement asserts that the unipotent radical acts transitively on split
  components; uniqueness of the conjugating point is not claimed.

## The proof

The proof is the anonymous constructor of the five published component theorems, in the order
of the conjunction:

| Conjunct | Theorem used | Module |
| --- | --- | --- |
| `ParabolicSplitComponentLeviStatement` | `parabolicSplitComponentLevi` | [ParabolicSplitComponentLeviProof](ParabolicSplitComponentLeviProof.md) |
| `LeviSplitComponentRadicalStatement` | `leviSplitComponentRadical` | [LeviSplitComponentRadicalProof](LeviSplitComponentRadicalProof.md) |
| `ParabolicSplitComponentConjugacyStatement` | `parabolicSplitComponentConjugacy` | [ParabolicSplitComponentConjugacyProof](ParabolicSplitComponentConjugacyProof.md) |
| `LeviCentralizerCharacterizationStatement` | `leviCentralizerCharacterization` | [LeviCentralizerCharacterizationProof](LeviCentralizerCharacterizationProof.md) |
| `MinimalParabolicSplitComponentStatement` | `minimalParabolicSplitComponent` | [MinimalParabolicSplitComponentProof](MinimalParabolicSplitComponentProof.md) |

All five theorems are in the namespace `Langlands.GroupScheme` and the modules
`Langlands.GroupScheme.Rational.*` listed above. Each has exactly the type `<Conjunct>.{u}`, so
the term needs no rewriting or unfolding beyond the definition of
`ParabolicSplitComponentStatements` as a conjunction. The mathematical content is in those five
proofs; this module adds none.

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The five component proofs are the modules of the table above. The target statement is in
[ParabolicSplitComponentStatements](ParabolicSplitComponentStatements.md). This module
modifies neither the target nor any imported module.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.ParabolicSplitComponentLeviProof` | `parabolicSplitComponentLevi`; also brings in the target module `Langlands.GroupScheme.Rational.ParabolicSplitComponentStatements` |
| `Langlands.GroupScheme.Rational.LeviSplitComponentRadicalProof` | `leviSplitComponentRadical` |
| `Langlands.GroupScheme.Rational.ParabolicSplitComponentConjugacyProof` | `parabolicSplitComponentConjugacy` |
| `Langlands.GroupScheme.Rational.LeviCentralizerCharacterizationProof` | `leviCentralizerCharacterization` |
| `Langlands.GroupScheme.Rational.MinimalParabolicSplitComponentProof` | `minimalParabolicSplitComponent` |
