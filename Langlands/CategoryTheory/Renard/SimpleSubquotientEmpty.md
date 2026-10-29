# Renard A.VI.3: empty simple-subquotient classes detect zero objects

Author: Worker 595.

This proof targets exactly
`Langlands.Renard.SimpleSubquotientEmptyStatement` in an arbitrary abelian
category, retaining both source antecedents and independent universes `w`,
`v`, `u`. It imports the published statement and `SimpleQuotient` modules
without modifying either pair or any of their dependencies.

The exported constant has the complete unapplied type

```lean
Langlands.Renard.simpleSubquotientEmpty.{w, v, u} :
  (C : Type u) → [Category.{v} C] → [Abelian C] →
    Langlands.Renard.SimpleSubquotientEmptyStatement.{w} C
```

The named proposition unfolds to

```lean
IsSourceGrothendieck.{w} C → SourceAB6 C →
  ∀ X : C, simpleSubquotientClasses X = ∅ ↔ IsZero X
```

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, Appendix A.VI.3,
printed pages 263–264 / PDF269–270. The source's unnumbered Lemma (ii) on
PDF270 says that the simple-subquotient classes are empty exactly for a zero
object. Both pages were read completely and the Lemma was visually checked.
The canonical local finite-type condition AB6 and the source Grothendieck
context are introduced at the end of PDF269.

The public Appendix A discrepancy note was read. The supplementary registered
`renard-2010-corrections-complements`, PDF18–19, replaces a sequence by a chain
in the preceding Proposition's Zorn argument. The inspected entries do not
correct this Lemma. This is a bounded observation about the separate 2010
errata. The original 2026 file has SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`;
the supplementary errata have SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
The retained original files are
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`
and
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.

For the forward direction, emptiness excludes every simple actual cokernel
of an inclusion between subobjects of `X`. If `X` were not finite type, the
published `nonFiniteTypeSimpleSubquotient` would supply precisely such a
cokernel, using the two retained source antecedents. Thus `X` is finite type.
If `X` were nonzero, the published
`exists_simple_cokernel_of_finiteType` would give a subobject `P` with simple
`cokernel P.arrow`. The top subobject's arrow is an isomorphism, and the actual
inclusion `Subobject.ofLE P ⊤ le_top` followed by that arrow is `P.arrow`.
`cokernelCompIsIso` and `cokernelIsoOfEq` identify its cokernel with
`cokernel P.arrow`. Transporting simplicity by `Simple.of_iso` contradicts
emptiness. The published simple-quotient results are reused by Lean name;
their Zorn and AB6 witness constructions are not repeated here.
That published dependency credits Worker 6 for its proof draft and Worker 961
for its check and submission; they are cited here for the imported mathematics.
The finite-type dichotomy and the top-subobject cokernel comparison in this
unit are internal elaborations of the source argument.

For the reverse direction, the subobjects of a zero object form a
subsingleton. Any nested subobjects `A ≤ B` therefore agree, so their actual
inclusion is an identity and hence an epimorphism. Its cokernel is zero by
`isZero_cokernel_of_epi`, contrary to `Simple.not_isZero`. This excludes
every class in the defining set.

These arguments elaborate the source's appeal to the preceding simple-quotient
result. They use actual subobjects, inclusions and cokernels, and the existing
quotient of objects by isomorphism. There is no finite-type or finite-length
hypothesis on `X`, no added smallness, generator, separator, concreteness or
module-category hypothesis, and no identification of the independent family,
Hom and object universes. Clauses (i), (iii) and the conjunction of the three
identities remain separate obligations.

The approved Lean service compiled this module and a private inspection
module with zero errors and warnings, diagnostic
`1a2003ef-92e8-4299-81a8-b84b826e1b1f`. The inspection printed the complete
unapplied theorem type and the target's body, checked direct assignments of the
unapplied theorem to both the named target and its expanded telescope, and
reported independent universe parameters `w`, `v`, `u`. The theorem depends
only on `propext`, `Classical.choice` and `Quot.sound`. These development
checks are separate from the staged candidate's machine validation, independent
semantic review and publication.
