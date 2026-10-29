# Renard A.VIII.2: proof of presentations by two coproducts of a generator

Authors: Worker 691 (Lean proof, source recheck and proof documentation),
Worker 945 and Worker 6 (published statement and categorical proof outline
reused from the task context and statement documentation).

This proof module imports the published
`Langlands.CategoryTheory.Renard.GeneratorPresentationStatements` and proves
its exact target `Langlands.Renard.GeneratorPresentationStatement`.
The theorem is `Langlands.Renard.generatorPresentation`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, A.VIII.2, final unnumbered lemma
on printed page 267 / PDF page 273. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`; retained original
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 691 reread the entire extracted page and its rendered image for this
proof. The source assumes a small progenerator in the surrounding cocomplete
abelian setting and ends with a right-exact row of two coproducts of `P`
followed by the given object and zero.

The supplementary source `renard-2010-corrections-complements`, retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was reread on PDF pages 18–19. These entries correct earlier exactness,
criterion-direction and smallness wording; they give no correction to this
presentation argument. No project `notes/errata` directory exists in the
inspected Library base. These are bounded source observations.

The published statement is an internal strengthening: it assumes only
`HomGenerator P` and coproducts indexed in the Hom universe. The proof below
establishes exactly that strengthening. Its categorical evaluation route
replaces the source's indexing by elements of an arbitrary object with
indexing by actual morphisms from `P`. The proof outline in the task context
and the published statement documentation supplied this route. The source's
smallness, projectivity and full cocompleteness are not needed for it.

## Declarations and universes

All declarations are in namespace `Langlands.Renard`. Their common context is

```lean
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
```

The complete theorem headers are

```lean
theorem homGenerator_isSeparator {P : C} (hP : HomGenerator P) :
  IsSeparator P

theorem homGenerator_epi_evaluation [HasCoproducts.{v} C] {P : C}
    (hP : HomGenerator P) (M : C) :
  Epi (Sigma.desc fun a : P ⟶ M => a)

theorem generatorPresentation [HasCoproducts.{v} C] (P : C) :
  GeneratorPresentationStatement P
```

In particular the complete type of the final theorem, before application, is

```lean
{C : Type u} → [Category.{v} C] → [Abelian C] →
  [HasCoproducts.{v} C] → (P : C) → GeneratorPresentationStatement P
```

There are no further section parameters. The object universe `u` and Hom
universe `v` are independent. Both index types constructed below lie in
`Type v`. The target statement and its imported Lean/Markdown pairs are
reused unchanged.

## Implemented proof

First `homGenerator_isSeparator` unfolds the published generator hypothesis
as faithfulness of the actual integer-module Hom functor. This functor is
the composite of `preadditiveCoyonedaObj P` with restriction of scalars along
`Int.castRingHom (End P)ᵐᵒᵖ`. Mathlib's `Functor.Faithful.of_comp` therefore
gives faithfulness of `preadditiveCoyonedaObj P`. Applying
`isSeparator_iff_faithful_preadditiveCoyonedaObj` proves `IsSeparator P`.
This helper establishes only the needed direction of the separate comparison
statement.

Next `homGenerator_epi_evaluation` applies `isSeparator_iff_epi` to this
separator. For every `M`, the resulting map is precisely

```lean
Sigma.desc fun a : P ⟶ M => a
```

from the chosen coproduct of one copy of `P` for each morphism `P ⟶ M`.
The coproduct exists by `HasCoproducts.{v} C`.

For `generatorPresentation`, fix `hP : HomGenerator P` and `M : C`. Set
`I := P ⟶ M` and let `g` be the evaluation epimorphism. Form the actual
categorical kernel `kernel g`. Set `J := P ⟶ kernel g` and let `e` be the
evaluation epimorphism onto this kernel. Define `f := e ≫ kernel.ι g`.
Associativity and `kernel.condition` prove `h : f ≫ g = 0`.

To prove `(ShortComplex.mk f g h).Exact`, the code applies Mathlib's
`ShortComplex.exact_iff_epi_kernel_lift`. Cancellation of the monomorphism
`kernel.ι g`, followed by `kernel.lift_ι`, identifies `kernel.lift g f h`
with `e`. The preceding evaluation lemma makes `e` epi and hence proves
exactness. The same lemma applied to `M` proves the additional conclusion
`Epi g`. These are the existential witnesses required by the target.

The Mathlib inputs are reused by name at prepared commit
`5ed2965256430c3649e86755f9576b54eca72435`: the faithful-composite lemma in
`CategoryTheory/Functor/FullyFaithful.lean`, the separator comparison in
`CategoryTheory/Generator/Preadditive.lean`, the evaluation criterion in
`CategoryTheory/Generator/Basic.lean`, and the kernel-lift exactness criterion
in `Algebra/Homology/ShortComplex/Exact.lean`. Their relevant source proofs
were read. Kernels, coproducts and exactness are Mathlib's actual categorical
constructions and predicates.

This focused proof does not establish the complete generator/cogenerator
comparison aggregate, smallness or finite-support characterizations,
finite-type comparisons, the regular-module converse, or the equivalence
with modules over `End P`. Those remain separate parent obligations.
