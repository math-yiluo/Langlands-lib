# Renard A.I.3: finite type and finite subcovers

This module defines the proposition `Langlands.Renard.FiniteTypeFiniteSubcoverStatement C`. It states, for every actual object `X` of `C`,

```lean
Langlands.Renard.IsFiniteTypeObject X ↔
  Langlands.Renard.HasFiniteSubcoverProperty X
```

The governing original is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, A.I.3, printed pages 248–249 / PDF254–255. Registered source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, retained at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`. Both original pages were read and visually inspected. The chain definition occurs at the bottom of PDF254. The sentence announcing a characterization by a compactness property begins there, and the finite-cover condition itself is at the top of PDF255. Renard phrases that condition as "X is of finite type if ..."; because it follows the announcement "On peut caractériser les objets de type fini par une propriété de compacité", it is read as an equivalence with the chain definition, not merely as a sufficient condition. Renard cites bibliography [37], Pareigis, *Categories and Functors* (1970), 4.10 Theorem 1. That cited book was not read for this unit and supplies no checked proof evidence here.

## Exact imported predicates and scope

The only import is the unchanged published `Langlands.CategoryTheory.RenardFiniteType`. Both sides use its existing predicates and Mathlib's actual `Subobject X` with its categorical factorization order.

`IsFiniteTypeObject X` asserts `HasSubobjectUnions X` and says that every nonempty chain of subobjects different from top fails to have top as a least upper bound. `HasSubobjectUnions X` asserts existence of a least upper bound for every subset of the actual subobject type, including the empty subset.

`HasFiniteSubcoverProperty X` asserts the same union existence and says that each subset `S : Set (Subobject X)` with `IsLUB S ⊤` contains a finite subset with the same least upper bound. The finite subset is represented by `T : Finset (Subobject X)` with `(T : Set (Subobject X)) ⊆ S` and `IsLUB (T : Set (Subobject X)) ⊤`. The cover and finite subcover may be empty. No family-size restriction or nonemptiness condition is added to this part.

The source speaks of families `(A_i)` and of finitely many members `A_{i_1}, …, A_{i_n}`. A family has the same upper bounds as its range, so it covers `X` exactly when its range `S` satisfies `IsLUB S ⊤`. Finitely many members of a family form a finite subset of that range, and every finite subset of the range arises this way. The set formulation is therefore equivalent to the source's family formulation, and repeated members play no role.

The full declaration has `C : Type u` and an actual `Category.{v} C`, with independent object and Hom universes. It returns `Prop` and quantifies over every `X : C`. The local union-existence conjuncts express the source's standing assumption for the object in question. In particular, each implication preserves that existence assertion. The statement requires no category-wide union hypothesis on unrelated objects and makes no claim that unions exist in an arbitrary category.

There is no abelian, zero-object, smallness, well-poweredness, Grothendieck, local finite-type, Noetherian, finite-presentability or module assumption. No complete-lattice instance or alternate order on subobjects is chosen. The proposition does not assume the desired equivalence as a hypothesis.

## Source conventions and repairs

The imported finite-type Markdown documents the repairs already made to the source wording. At the top of PDF255, the initial cover equation prints `A` although both the object being characterized and the final finite-cover equation use `X`. Here the cover equation is `IsLUB S ⊤`.

Chains in the finite-type predicate are nonempty. If the empty chain were included, a zero object would fail the condition because its empty union is top, contrary to the source's finitely generated module example. Empty finite subcovers remain permitted, so the characterization retains that case.

Properness means that the subobject class differs from top, equivalently that its particular inclusion is not an isomorphism. It does not mean that its domain object is abstractly nonisomorphic to `X`. These conventions are internal mathematical diagnoses, not author-issued errata, and this unit changes none of the published predicates.

The published `notes/renard/appendix-a-corrections.md` was consulted; it concerns three other Appendix A passages. A bounded lookup in the workspace, project notes and pinned Library found no dedicated `notes/errata/renard-2026-representations-groupes-reductifs-padiques.md`. The supplementary registered 2010-edition author corrections, source `renard-2010-corrections-complements`, SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, at `/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`, were consulted at PDF18–19. Those pages do not address these A.I.3 repairs. This limited lookup does not assert that every possible erratum was found.

## Statement and proof boundary

The file defines the equivalence as a proposition and proves neither implication. Its substantive proof is a separate obligation over this exact statement once published. In particular, the general chain-to-finite-cover implication must still be justified for covers of arbitrary cardinality. Mathlib's directed-compactness API and special module comparisons cannot silently stand for that missing argument.

The general statement can specialize to actual module categories without assuming them in its type. Worker 709's actual unital-module comparison remains separate. The Noetherian characterizations, compact-element comparison, source Noetherian-ring convention and nonunital category adapters also remain separate obligations.

## Provenance and checks

Worker 6 drafted this pair as shared draft revision 1 of statement task `4707845d-d085-45a0-b8ce-4621924b23e9`. Worker 840 reread PDF254–255 against it, refined this Markdown and submitted the pair. The Lean file is unchanged from that draft.

A development check in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the module with no diagnostics and reported `statement_returns_prop: true`. It gave the unapplied type `(C : Type u) → [Category.{v, u} C] → Prop`. A private check confirmed by `rfl` that the body unfolds to the objectwise equivalence above, with both published predicate bodies fully expanded. These development checks establish no independent acceptance or publication.
