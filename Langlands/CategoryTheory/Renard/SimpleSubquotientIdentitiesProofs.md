# Renard A.VI.3: all three simple-subquotient identities

Author: Worker 973.

This module proves `Langlands.Renard.simpleSubquotientIdentities`, whose
complete unapplied type is

```lean
Langlands.Renard.simpleSubquotientIdentities.{w, v, u} :
  ∀ (C : Type u) [Category.{v} C] [Abelian C],
    Langlands.Renard.SimpleSubquotientIdentitiesStatement.{w} C
```

The target is the unchanged published proposition
`Langlands.Renard.SimpleSubquotientIdentitiesStatement` in
`Langlands.CategoryTheory.Renard.SimpleSubquotientIdentitiesStatements`.
It is exactly the conjunction, in source clause order,

```lean
SimpleSubquotientSubobjectQuotientStatement.{w} C ∧
  SimpleSubquotientEmptyStatement.{w} C ∧
    SimpleSubquotientSumStatement.{w} C
```

The family universe `w`, Hom universe `v` and object universe `u` stay
independent. The statement pair and everything it imports are unchanged.

## Source

The governing original is the unnumbered three-part Lemma in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, Appendix A.VI.3, printed page 264 / PDF270. Its Grothendieck
and AB6 hypotheses are introduced at the end of printed page 263 / PDF269.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`;
original file:
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`;
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Lemma's clauses are (i) `JH(M) = JH(M') ∪ JH(M/M')` for a subobject
`M'`, (ii) `JH(M) = ∅` exactly when `M = 0`, and (iii) `JH(∑ M_i)` is the
union of the `JH(M_i)` for a family of subobjects.

This unit adds no new mathematics about those clauses. The source reading,
the correspondence of the three targets with the Lemma and the bounded
supplementary 2010 errata check are recorded in the published statement
Markdown `SimpleSubquotientIdentitiesStatements.md`. They are not repeated
here. The internal routes of the three component proofs were not
re-derived for this unit; they are cited from their published modules.

## Proof

The proof is conjunction introduction from three published theorems,
used by Lean name and each applied to `C` at the same family universe `w`:

- clause (i): `Langlands.Renard.simpleSubquotientSubobjectQuotient`, from
  `Langlands.CategoryTheory.Renard.SimpleSubquotientSubobjectQuotient`,
  proves `SimpleSubquotientSubobjectQuotientStatement.{w} C`
  (Worker 695);
- clause (ii): `Langlands.Renard.simpleSubquotientEmpty`, from
  `Langlands.CategoryTheory.Renard.SimpleSubquotientEmpty`, proves
  `SimpleSubquotientEmptyStatement.{w} C` (Worker 595);
- clause (iii): `Langlands.Renard.simpleSubquotientSum`, from
  `Langlands.CategoryTheory.Renard.SimpleSubquotientSum`, proves
  `SimpleSubquotientSumStatement.{w} C` (Worker 695 and Worker 595).

The proof term is the anonymous constructor

```lean
⟨simpleSubquotientSubobjectQuotient.{w} C, simpleSubquotientEmpty.{w} C,
  simpleSubquotientSum.{w} C⟩
```

which Lean elaborates as the right-nested pair matching the target's
`A ∧ (B ∧ C)` shape. Each component has exactly the type of the matching
conjunct, so no unfolding, rewriting or argument adaptation is needed.

Each component proposition still retains its source antecedents
`IsSourceGrothendieck.{w} C` and `SourceAB6 C` inside it. No antecedent
is discharged, weakened or assumed here, and no conclusion of a clause is
taken as a hypothesis. In clause (iii) the coproduct instance is still
obtained inside the proposition from `hG.1`, and every `I : Type w` is
covered, including the empty type, exactly as in the published component.

There is no added finite-type, finite-length, smallness,
well-poweredness, local-smallness, concrete-category, module, generator
or separator hypothesis. This aggregate does not prove the later A.IX
results, supported-sum or decomposition statements, or any other part of
the book.

## Checks

The approved Lean service compiled this module in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with zero errors and warnings
(diagnostic `8ce7b758-2228-4f3d-b437-dabf0e73e351`). Its inspection
reports a theorem with level parameters `w`, `v`, `u`, depending only on
`propext`, `Classical.choice` and `Quot.sound`.

A private inspection module (diagnostic
`67429d94-73c0-40e7-ac24-06596b7cf5f1`, zero errors and warnings) printed
the complete unapplied type and the body of the theorem and the body of
the target. It assigned the unapplied constant `@simpleSubquotientIdentities`
directly to both the named target telescope and the fully expanded
three-clause proposition, and instantiated it at fresh independent
universes. All checks passed. These are development checks, separate
from the staged candidate's machine validation, independent semantic
review and publication.
