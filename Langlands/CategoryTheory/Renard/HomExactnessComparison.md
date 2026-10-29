# Renard A.VIII.2: proof of Hom left exactness and lifting comparisons

Authors: Worker 595 (Lean proof, source checks, declaration checks and
documentation); Worker 923 (proof navigation in the task context).

This proof unit proves the unchanged published
`Langlands.Renard.HomExactnessComparisonStatement P`, with one named theorem
for each of its four clauses. All five public theorems have the common
context `{C : Type u} [Category.{v} C] [Abelian C] (P : C)`, with independent
universes `v` and `u` and no additional hypothesis.

The module is
`Langlands.CategoryTheory.Renard.HomExactnessComparison`. Its exported
theorems, in namespace `Langlands.Renard`, have exactly these result types:

| Theorem | Published proposition proved |
| --- | --- |
| `covariantHomLeftExact` | `CovariantHomLeftExactStatement P` |
| `contravariantHomLeftExact` | `ContravariantHomLeftExactStatement P` |
| `homProjectiveComparison` | `HomProjectiveComparisonStatement P` |
| `homInjectiveComparison` | `HomInjectiveComparisonStatement P` |
| `homExactnessComparison` | `HomExactnessComparisonStatement P` |

## Implemented proof

The left exactness clauses use the published comparison of each actual
integer-module Hom functor with the additive-group-valued Hom functor.
Mathlib's preadditive Yoneda limit-preservation instances show that the
composite preserves finite limits. The forgetful functor from integer
modules to additive commutative groups reflects limits; consequently the
integer-module Hom functor itself preserves finite limits. The published
`sequenceLeftExactFiniteLimits` gives the required sequence condition.
The contravariant proof works directly on the opposite category.

A private helper proves that a left sequence exact additive functor
between abelian categories is two-sided sequence exact if and only if
it preserves epimorphisms. In one direction, the right sequence condition
on short exact complexes implies epimorphism preservation by Mathlib's
`preservesEpimorphisms_of_preserves_shortExact_right`. Conversely, left
exactness supplies exactness of the mapped short exact complex, and
epimorphism preservation supplies its final epimorphism. Entry 1 to entry 2
of `preservesFiniteColimits_tfae` extends this to every exact input with
final epimorphism, giving the published right sequence condition. This
helper takes left exactness as an input; each public comparison supplies
that input using the corresponding left exactness theorem proved above.

A second private helper transfers epimorphism preservation through the
forgetful functor from integer modules to types, which preserves and
reflects epimorphisms. The actual integer-module Hom functors become
the type-valued coyoneda and yoneda functors definitionally after this
forgetful functor. Mathlib's
`Projective.projective_iff_preservesEpimorphisms_coyoneda_obj` and
`Injective.injective_iff_preservesEpimorphisms_yoneda_obj` then give the
projective and injective comparisons. The aggregate pairs the four
clauses in the published order.

The code reuses the published
`preadditiveCoyonedaInt_comp_forget₂` and
`preadditiveYonedaInt_comp_forget₂` equalities from `HomFunctors` and
`sequenceLeftExactFiniteLimits` from `FinitePreservation` by Lean name.
The finite-limit reflection step is
`preservesFiniteLimits_of_reflects_of_preserves`, using
`ModuleCat.forget₂_reflectsLimits`. The limit-preservation instances are
`preservesLimits_preadditiveCoyoneda_obj` and
`preservesLimits_preadditiveYoneda_obj`. Epimorphism transfer uses
`ModuleCat.forget_preservesEpimorphisms` and
`Functor.preservesEpimorphisms_of_preserves_of_reflects`; faithfulness of
the forgetful functor supplies reflection of epimorphisms.

The proof establishes the full published sequence predicates, including
inputs whose other endpoint is unrestricted. It does not replace those
predicates by preservation of short exact sequences: the private
exactness helper uses Mathlib's equivalence to extend from short exact
inputs to the full right sequence predicate.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, A.VIII.2, printed page 267 /
PDF page 273, with the additivity and opposite-category convention on
printed page 266 / PDF page 272. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both original pages were reread. The supplementary registered
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was reread at PDF pages 18–19. These appendix corrections do not alter
the Hom left exactness or exact-Hom definitions used here. The retained
originals are respectively
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`
and
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.

The two left exactness assertions are explicit in the source. The
projective and injective comparisons and the helper lemmas are derived
identifications with Mathlib, as already specified by the published
statement unit. The proof uses Mathlib at commit
`5ed2965256430c3649e86755f9576b54eca72435` by import and declaration name.

The Mathlib sources below are registered, retained under the prepared
Mathlib source tree and reused without copying. They are released under
Apache 2.0; their original author lists remain in those files.

| Registered source | Relevant declarations or section | SHA256 |
| --- | --- | --- |
| `mathlib-preadditive-yoneda-limits-5ed296525643` | The four preadditive Yoneda limit-preservation instances | `c2410d0736a086a3fb071623ff69c3a73e166d7936178aada9194f47a3f6deab` |
| `mathlib-modulecat-abelian-5ed296525643` | `forget₂_reflectsLimits` in `ReflectsLimits` | `10907136dd466a5226a030128549b2314c11c92e7600f04eabbb30ab873a6ff5` |
| `mathlib-finite-preservation-5ed296525643` | `preservesFiniteLimits_of_reflects_of_preserves` | `b1089a0b81f0f9c3ac0ae66c089db0b34c8d60f5fa23a077bd0754588e719cee` |
| `mathlib-shortcomplex-exactfunctor-5ed296525643` | `preservesEpimorphisms_of_preserves_shortExact_right`; entries 1 and 2 of `preservesFiniteColimits_tfae` | `0d767b2a3d4473a0b40ed4b47a220915d0400c9b049931256ff35294b0a50414` |
| `mathlib-modulecat-epimono-5ed296525643` | `epi_iff_surjective`, `forget_preservesEpimorphisms` | `9a749dbb0a1452aad101a59b4920a5d40d57daf93eb2a9dd83afb8633c2201bc` |
| `mathlib-functor-epimono-5ed296525643` | Epimorphism preservation by composition and reflection | `5494fb4b5b8ba3e7caaff0f3774ebf4cacbb374e93867ae7435bb3f8a52e314e` |
| `mathlib-projective-basic-5ed296525643` | `Projective.projective_iff_preservesEpimorphisms_coyoneda_obj` | `a5d71333bc05cbced91fd166427870229550b1d9f461644ecbbacd0c040f3ddb` |
| `mathlib-injective-basic-5ed296525643` | `Injective.injective_iff_preservesEpimorphisms_yoneda_obj` | `0aed70a02680fd82da437ac56a2702a2fbb45338ee399781f92d3ce38933bb22` |

## Context and boundary

The category is arbitrary abelian; there is no smallness,
enough-projectives, enough-injectives or module-category premise.
The object `P` is arbitrary, and projectivity and injectivity occur only
inside the respective comparison conclusions. For the contravariant
clauses, the source's convention is implemented literally as sequence
exactness of the actual functor on `Cᵒᵖ`. The restricted scalars are
integers; neither proof assumes commutativity of `End P`.

The module introduces two private helper lemmas and the five named
public theorems. It installs no global instances and leaves the target
Lean/Markdown pair and every imported pair unchanged. Complete unapplied
declaration checks assign all five theorem constants to the expected
outer telescope. The aggregate depends only on `propext`,
`Classical.choice` and `Quot.sound`. These development checks do not
replace independent semantic review or official exact-target validation.

Generator and cogenerator comparisons, smallness, presentations and
module-category equivalence remain separate obligations.
