# Renard A.VI.2(10): complete abelian categories have all limits

Authors: Worker 800 and Worker 6. Worker 6 wrote the target specification,
including the two implications, the size bound `HasLimitsOfSize.{w, w}` and
the expected proof route, and checked in a private probe that the proposed
types elaborate. Worker 800 read the original passage and the errata
independently and wrote this Lean/Markdown pair. This unit states
A.VI.2(10). It proves nothing; the proof is a separate obligation.

## Original and reading record

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, Appendix A.VI.2(10), printed page 263 / PDF
page 269. Registered source ID:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, which was
recomputed at authoring. The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF pages 268–270 were read, together with A.IV.1–A.IV.2 on PDF pages
262–263, which define diagrams, limits, colimits and inverse and direct
systems.

The assertion reads:

> — 10. Supposons que 𝒜 soit complète (resp. cocomplète). Alors tout
> diagramme D : I → 𝒜, admet une limite (resp. colimite). En particulier,
> 𝒜 admet des limites inverses (resp. directes).

In translation: suppose that 𝒜 is complete (resp. cocomplete). Then every
diagram D : I → 𝒜 has a limit (resp. colimit). In particular, 𝒜 has inverse
(resp. direct) limits.

Here 𝒜 is the abelian category of A.VI.2. Immediately above (10), on the same
page, an abelian category satisfying AB4 (every family of objects has a
product) is called *complete*, and one satisfying AB4\* (every family of
objects has a direct sum) is called *cocomplete*. These conventions are the
published predicates `Langlands.Renard.IsSourceComplete` and
`Langlands.Renard.IsSourceCocomplete` of
`Langlands.CategoryTheory.RenardGrothendieckAxioms`, which this unit imports
and uses unchanged. On PDF262, A.IV.1 calls a functor `D : I → 𝒞` a
*diagram* in 𝒞 with scheme `I`, where `I` is an arbitrary category.

Errata check: no separate project errata note for the 2026 edition exists in
the published Library notes. The published note
`notes/renard/appendix-a-corrections.md` concerns A.III.1, A.IV.1–A.IV.2 and
A.VI.1. Its A.IV entries (direction typos in the universal-property arrows
and the constant-functor bijection for nonempty indices) do not affect (10),
which uses only the notions of limit and colimit; see "Limits and colimits"
below. The appendix entries of the registered author correction list for the
2010 edition, `renard-2010-corrections-complements` (SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`), PDF
pages 18–19, were read. None concerns (10). Its one nearby entry, page 298
line 6 "limite" → "colimite" in the description of direct limits (A.IV.2), is
already incorporated in the 2026 text on PDF263. The author's web page was
fetched on 27 October 2026; as in the registered snapshot
`renard-author-page-2026-10-26`, it gives a separate errata file only for the
2010 edition. This check does not establish that no later erratum exists. The
printed wording of (10) is not repaired here.

## Declarations

Module `Langlands.CategoryTheory.RenardCompletenessLimitsStatements` defines
three transparent `def`s returning `Prop`, in namespace `Langlands.Renard`.
Each takes an explicit `C : Type u` with instance arguments
`[Category.{v} C]` and `[Abelian C]`. Each carries `@[pp_with_univ]`, and its
universe parameters are in the order `w, v, u`, as for the predicates of
`RenardGrothendieckAxioms`; thus `SourceCompletenessLimitsStatement.{w} C`
fixes the family and diagram size `w`. Their complete types are as follows;
`lean_check` inspection of each reports level parameters `w, v, u` and a
`Prop`-valued statement.

```lean
Langlands.Renard.SourceCompleteHasLimitsStatement.{w, v, u} :
  (C : Type u) → [inst : Category.{v, u} C] → [Abelian C] → Prop
Langlands.Renard.SourceCocompleteHasColimitsStatement.{w, v, u} :
  (C : Type u) → [inst : Category.{v, u} C] → [Abelian C] → Prop
Langlands.Renard.SourceCompletenessLimitsStatement.{w, v, u} :
  (C : Type u) → [inst : Category.{v, u} C] → [Abelian C] → Prop
```

| Declaration in `Langlands.Renard` | Body |
| --- | --- |
| `SourceCompleteHasLimitsStatement.{w} C` | `IsSourceComplete.{w} C → HasLimitsOfSize.{w, w} C` |
| `SourceCocompleteHasColimitsStatement.{w} C` | `IsSourceCocomplete.{w} C → HasColimitsOfSize.{w, w} C` |
| `SourceCompletenessLimitsStatement.{w} C` | `SourceCompleteHasLimitsStatement.{w} C ∧ SourceCocompleteHasColimitsStatement.{w} C` |

The first two are the two halves of (10), separately reusable as proof
targets. The third is their conjunction at the same size `w`; it is the
combined proof target for A.VI.2(10).

The only hypotheses are the actual Mathlib `Abelian C` structure and the
respective published source predicate. Since `IsSourceComplete.{w} C` and
`IsSourceCocomplete.{w} C` are transparent abbreviations of
`HasProducts.{w} C` and `HasCoproducts.{w} C`, the first two bodies unfold,
by `Iff.rfl`, to `HasProducts.{w} C → HasLimitsOfSize.{w, w} C` and
`HasCoproducts.{w} C → HasColimitsOfSize.{w, w} C`. No `WellPowered`,
`LocallySmall`, generator, separator, exactness, module-category,
small-category or finite-dimensionality hypothesis is placed on `C`. The
stronger Mathlib class `IsGrothendieckAbelian` is not used, and the source
predicates are not identified with Mathlib's exactness classes `AB4OfSize`
or `AB4StarOfSize`, which state that coproducts or products are exact; source
AB4 and AB4\* assert only existence.

## Limits and colimits

The conclusions are Mathlib's `HasLimitsOfSize.{w, w} C` and
`HasColimitsOfSize.{w, w} C`
(`Mathlib/CategoryTheory/Limits/HasLimits.lean`). The first says: for every
`J : Type w` with `Category.{w} J`, every functor `F : J ⥤ C` has a limit,
that is, `HasLimit F`, which is the proposition `Nonempty (LimitCone F)`
(`HasLimit.exists_limit`) that some cone over `F` is a limit cone. The
colimit version is dual. These are existence statements about actual Mathlib
functors, cones and limit cones; no limit is chosen and no replacement
functor is introduced.

The source defines a limit of `D : I → 𝒞` as a universal pair consisting of
a constant functor and a natural transformation, and then, more concretely,
as an object with compatible morphisms to every `D(i)` and the universal
factorization property. The published unit
`Langlands.CategoryTheory.Renard.ConeBridge` identifies this concrete
universal property with Mathlib's `IsLimit` and `IsColimit`
(`Langlands.CategoryTheory.Renard.coneUniversal_iff_nonempty_isLimit` and
`coconeUniversal_iff_nonempty_isColimit`), and the corrections note above
records why the cone form, rather than the constant-functor form, is the
right reading for arbitrary index categories. This unit does not import that
bridge; Mathlib's `HasLimit` is the formalization of "admet une limite".

## Sizes and universes

The source says "every family" in AB4 and AB4\* and "every diagram" in (10),
without a size bound. Following `RenardGrothendieckAxioms`, the hypotheses fix
a family size `w`: `IsSourceComplete.{w} C` means that products of families
indexed by `I : Type w` exist. The conclusions concern diagrams whose index
category has objects in `Type w` and morphisms in `Type w`. The family size
`w`, the Hom universe `v` and the object universe `u` of `C` are independent;
in particular `C` need not be small or locally small relative to `w`.

The diagrams covered include, at size `w`:

- the empty diagram (for example `Discrete PEmpty.{w + 1}`), whose limit is a
  terminal object and whose colimit is an initial object;
- disconnected diagrams, such as discrete ones, whose limits and colimits are
  products and coproducts. Thus `HasLimitsOfSize.{w, w} C` gives back
  `HasProducts.{w} C`;
- parallel pairs, giving equalizers and coequalizers. The walking parallel
  pair is neither filtered nor cofiltered: its two distinct arrows
  `zero ⟶ one` are coequalized by no arrow out of `one` and equalized by no
  arrow into `zero`, since the only such arrows are identities;
- cospans `i → p ← j`, giving pullbacks, and dually spans, giving pushouts.
  The walking cospan has the terminal object `p`, so it is filtered;
- inverse and direct systems, described in the next section. For a nonempty
  directed order `I`, the index category `I` of a direct system is filtered,
  while the index category `Iᵒᵖ` of an inverse system is cofiltered and need
  not be filtered. For example, take `I = {a, b, t}` with only `a < t` and
  `b < t`: it is directed, but in `Iᵒᵖ` no object receives arrows from both
  `a` and `b`.

Index categories in a smaller universe, such as Mathlib's
`WalkingParallelPair : Type` and `WalkingCospan : Type`, are reached through
Mathlib's `hasLimitsOfSizeShrink` and `hasColimitsOfSizeShrink`, which pass
from a size bound to every smaller one.

No filteredness, connectedness or nonemptiness condition is imposed on the
index category. Conversely, nothing is stated about diagrams of larger size:
the statements at size `w` say nothing about index categories whose objects
or morphisms lie in a universe not below `w`, and no statement is made for
all universes at once. Mathlib's `hasLimitsOfSizeShrink` only goes down.

## Inverse and direct systems

The source's final sentence is a special case of the main statements. In
A.IV.1, example 5 (PDF263), an inverse (projective) system is a functor out
of a filtered increasing ordered set `I`, viewed as a category in which
`i ≤ j` gives a morphism `j → i`; its inverse limit is the limit of that
functor. In A.IV.2 (PDF263), a direct (inductive) system is a functor out of
the same kind of ordered set with `i ≤ j` giving `i → j`; its direct limit is
the colimit.

In Mathlib, a preorder `I` is a category with a morphism `i ⟶ j` exactly when
`i ≤ j`. So for `I : Type w` with `[Preorder I]` and
`[IsDirected I (· ≤ ·)]`, a source inverse system is a functor `Iᵒᵖ ⥤ C` and
a source direct system is a functor `I ⥤ C`. Both `I` and `Iᵒᵖ` have objects
in `Type w` and morphisms in `Type w`, so `HasLimitsOfSize.{w, w} C` gives a
limit of every inverse system and `HasColimitsOfSize.{w, w} C` gives a
colimit of every direct system indexed at size `w`. A private Lean
diagnostic, not part of this unit, checked these two consequences; the
existence of limits or colimits in the empty, discrete, parallel-pair and
cospan cases above (the last two through `hasLimitsOfSizeShrink` and
`hasColimitsOfSizeShrink`); the recovery of `HasProducts.{w} C`;
`IsFiltered WalkingCospan`, via Mathlib's `IsFiltered.of_isTerminal`; and,
by Mathlib instances, `IsFiltered I` and `IsCofiltered Iᵒᵖ` for a nonempty
directed `I`. It did not check the counterexample above in Lean. The main statements are not restricted to these
systems and impose no directedness.

## Equalizers and the later proof

For an abelian category, Mathlib provides equalizers and coequalizers through
the instances `CategoryTheory.Abelian.hasEqualizers` and
`CategoryTheory.Abelian.hasCoequalizers`
(`Mathlib/CategoryTheory/Abelian/Basic.lean`): the equalizer of `f, g` is the
kernel of `f - g`. These finite limits and colimits are what the standard
construction of a limit as an equalizer of two maps between products, and
dually of a colimit as a coequalizer of two maps between coproducts, needs in
addition to the source hypothesis. Mathlib's
`has_limits_of_hasEqualizers_and_products` and
`has_colimits_of_hasCoequalizers_and_coproducts`
(`Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean`)
are the expected proof route. This unit claims no proof: the statements are
propositions, and their proof is a separate task.

## Scope and provenance

The file imports only `Langlands.CategoryTheory.RenardGrothendieckAxioms`. It
defines the three propositions and contains no theorems, proof holes or new
axioms, and it does not assume any of its conclusions. The names, the size
convention `HasLimitsOfSize.{w, w}` and the split into two implications and
their conjunction follow Worker 6's task specification for task
`11f873e9-41f9-4745-bb70-e0e2748a9b61`. The size bound itself is a
formalization choice inherited from `RenardGrothendieckAxioms`, since the
source does not bound "every family". The existence of sums of arbitrary
families of subobjects, the comparisons with Mathlib's AB5 and Grothendieck
classes, and A.VI.3 AB6 remain separate obligations.
