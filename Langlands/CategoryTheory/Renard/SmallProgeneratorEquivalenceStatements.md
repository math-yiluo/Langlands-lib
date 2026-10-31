# Renard A.VIII.2: the actual small-progenerator equivalence

Authors: Worker 6 (statement design, implementation and documentation);
Worker 923 (independent source and errata reread, contract type
ascription, Markdown revision, compilation and inspection).

This file states one theorem,
`Langlands.Renard.SmallProgeneratorEquivalenceStatement`, in module
`Langlands.CategoryTheory.Renard.SmallProgeneratorEquivalenceStatements`.
It supplies no proof, inverse functor or equivalence construction.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Complete PDF pages 272–273 (printed 266–267) were reread for this unit
by Worker 6 and, independently, by Worker 923.

The unnumbered **Théorème** in A.VIII.2 (Progénérateurs), printed page
267 / PDF page 273, reads:

> Soit A une catégorie abélienne, cocomplète, et admettant un petit
> progénérateur P. Alors A est naturellement équivalente à la catégorie
> des modules à droite unitaires sur l'anneau R_P = End_A(P),
> l'équivalence étant donnée par le foncteur Hom_A(P,•).

In English: let `A` be a cocomplete abelian category with a small
progenerator `P`. Then `A` is naturally equivalent to the category of
unital right modules over the ring `R_P = End_A(P)`, the equivalence being
given by the functor `Hom_A(P, •)`.

The same page defines a projective object, a generator, a small
projective and a small progenerator using the actual functor
`Hom_A(P, •)`. A.VIII.1, printed page 266 / PDF page 272, defines
exactness of a functor by both one-sided sequence conditions.

Renard refers to Pareigis [37], §4.11, Theorem 1 for this theorem and
gives no proof on the page. Neither Worker 6, the supplied draft's
author, nor Worker 923 has read Pareigis; no proof from it has been
checked for this unit.

The supplementary author errata for the 2010 edition,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were reread completely at PDF pages 18–19. The correction for the 2010
printed page 309, line 2, replaces the fixed object `X` by `P` in the
smallness definition `Hom(P, •)`. The governing 2026 text already prints
`P`. Those two pages give no correction to the equivalence theorem. This
observation is limited to those pages and that edition.

## Declaration

```lean
def SmallProgeneratorEquivalenceStatement (C : Type u) [Category.{v} C]
    [Abelian C] [HasCoproducts.{v} C] : Prop :=
  ∀ P : C, HomSmallProgenerator.{v} P →
    (preadditiveCoyonedaObj P : C ⥤ ModuleCat.{v} (End P)ᵐᵒᵖ).IsEquivalence
```

The type ascription on the functor is the contract's literal body. It
names the target category and elaborates to the same term as the bare
`preadditiveCoyonedaObj P`.

## Hypotheses

The hypotheses are the actual category `C`, its abelian structure, all
coproducts indexed by types in `Type v`, and the unchanged published
predicate `HomSmallProgenerator.{v} P` of
`Langlands.CategoryTheory.Renard.SmallProjective`. Write
`H = Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P`, the
actual integer-module Hom functor `C ⥤ ModuleCat.{v} ℤ`. The predicate is
the conjunction of three conditions:

- **projective** (`HomProjective P`): `SequenceExact H`. This keeps both
  one-sided conditions of A.VIII.1. Left exactness says that for every
  exact short complex `A → B → D` with `A → B` a monomorphism, the image
  under `H` is exact and `H` maps `A → B` to a monomorphism. Right
  exactness says the same with `B → D` an epimorphism and its image an
  epimorphism.
- **small** (the second half of `HomSmallProjective.{v} P`): for every
  `I : Type v`, `H` preserves colimits of shape `Discrete I`, that is,
  coproducts indexed by `I`.
- **generator** (`HomGenerator P`): `H` is faithful.

There is no assumed fullness, essential surjectivity or equivalence among
the hypotheses. The endomorphism ring is not assumed commutative or
nonzero.

`H` is the conclusion's functor with scalars restricted along
`ℤ → (End P)ᵐᵒᵖ`; the inspection below checks this by `rfl`.

## The functor and the right action

The conclusion uses Mathlib's existing
`CategoryTheory.preadditiveCoyonedaObj P : C ⥤ ModuleCat.{v} (End P)ᵐᵒᵖ`.

It sends `X` to the actual carrier `P ⟶ X` and sends `g : X ⟶ Y` to
postcomposition `f ↦ f ≫ g`. The left action of the opposite ring is
`MulOpposite.op r • f = r ≫ f`. In Mathlib's endomorphism ring,
`r * s = s ≫ r`, which is ordinary composition `r ∘ s`. So `End P` is
Renard's `R_P = End_A(P)`, and the action is the right action
`f · r = f ∘ r`. It satisfies `f · (r * s) = (f · r) · s` and
`f · 1 = f`. Thus `ModuleCat.{v} (End P)ᵐᵒᵖ` is the category of unital
right `End P`-modules, written as left modules over the opposite ring.
Mathlib modules are unital by definition.

`Functor.IsEquivalence F` is the proposition that the specified functor
`F` is faithful, full and essentially surjective. Once it holds,
Mathlib's `Functor.asEquivalence F` is an equivalence of categories
whose forward functor is `F` itself, definitionally, with a chosen
quasi-inverse and natural unit and counit isomorphisms. This is how the
statement renders the source's natural equivalence "given by the functor
`Hom_A(P, •)`". It does not assert a bare equivalence with some
unspecified functor.

## Size convention

The source has no universe notation. The object universe `u` is
independent of the Hom universe `v`. The ring `End P` and every Hom
carrier `P ⟶ X` are in `Type v`. Target module carriers and coproduct
indices are also in `Type v`, and the target category
`ModuleCat.{v} (End P)ᵐᵒᵖ` has objects in `Type (v + 1)`. The statement
does not replace `v` by `max u v`. It claims no equivalence with modules
whose carriers live in a larger universe.

Renard's "cocomplète" is read relative to the Hom size: colimits of
diagrams whose index category has objects and morphisms in `Type v`.
`[Abelian C] [HasCoproducts.{v} C]` is equivalent to this. An abelian
category has coequalizers, so Mathlib's
`has_colimits_of_hasCoequalizers_and_coproducts` gives
`HasColimitsOfSize.{v, v} C`. Conversely, that instance supplies
`HasCoproducts.{v} C`. Colimits indexed by all objects of `C` are not
required.

These sizes are the ones that the presentations in the theorem need.

- **Objects of `C`.** For `X : C`, the canonical map
  `∐ (fun _ : P ⟶ X => P) ⟶ X` is indexed by `P ⟶ X : Type v`. Its
  kernel is presented in the same way, indexed by `P ⟶ ker`. The public
  theorem `Langlands.Renard.generatorPresentation` uses exactly these
  coproducts to give a two-term presentation of every object by copies
  of a generator with indices in `Type v`.
- **Modules.** A module `M` with carrier in `Type v` has a free
  presentation whose index types are the carrier of `M` and the carrier
  of the relation kernel, both in `Type v`. The corresponding coproducts
  of copies of `P` exist in `C`, and cokernels exist because `C` is
  abelian.

No smallness requirement on subobjects is added, and `P` is the only
generator assumed.

No Grothendieck, AB5, AB6, enough-projectives, finite-type, Noetherian,
finite-dimensionality or nonzero-object premise is present. The
degenerate zero category and zero ring are included.

## Verification

Development checks used the approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Worker 6 reports exact entry
checks `60efaf4a-84c2-41d2-aef8-9314a5d3fff6` and
`a65a5a28-2730-4842-8389-65dba121082d`, and probes
`95383e65-ac94-4ac4-990c-058850437297` and
`aa603410-552c-4e5f-818a-b8f6f10833e8`, for the draft without the
ascription. All are reported clean.

Worker 923 checked the ascribed body. The draft statement check
(diagnostic `3e619238-62fb-4175-ab54-fb2e717eef17`) had no errors or
warnings. It returned a `Prop`, with level parameters `v u` and axioms
`propext`, `Classical.choice` and `Quot.sound`. The workspace check of
this exact pair (diagnostic `ec1c0531-34b8-4821-a73b-ef23049d0b71`)
gave the same result. A private inspection
module (diagnostic `bbe42771-81c5-4025-b1f0-a2e60e29c3d6`, no errors or
warnings) checked the following.

- It printed the declaration with explicit instances. The preadditive
  structure is `Abelian.toPreadditive`, the ring is
  `Preadditive.instRingEnd` with `MulOpposite.instRing`, and the
  conclusion is `Functor.IsEquivalence.{v, v, u, v + 1}`.
- It checked the complete unapplied telescope, and that the fully
  qualified contract body equals the definition by `rfl`.
- It unfolded `HomSmallProgenerator.{v} P` to the three conditions above
  by `Iff.rfl`.
- It checked that `preadditiveCoyonedaInt P` is
  `preadditiveCoyonedaObj P ⋙ ModuleCat.restrictScalars` along
  `Int.castRingHom` by `rfl`.
- It checked by `rfl` that the carrier is `P ⟶ X`, that the map is
  postcomposition, that `op r • f = r ≫ f` and that `r * s = s ≫ r`, and
  by `one_smul` that `1 • f = f`.
- It checked that `IsEquivalence` is equivalent to faithful, full and
  essentially surjective, and that `asEquivalence` has forward functor
  `preadditiveCoyonedaObj P` by `rfl`.
- It instantiated the statement at universes `(v, u) = (0, 1)`, `(2, 0)`
  and `(1, 5)`, and at `ModuleCat.{0} ℤ`.
- It checked the size-relative cocompleteness equivalence described
  above.

These are checks of the statement and its terms. They do not prove the
theorem.

## Separate obligations

The finite-subcoproduct characterization of small projectives, the
Grothendieck finite-type comparison and the regular-module
small-progenerator remark have their own statements and proof branches.
`Langlands.Renard.generatorPresentation` does not itself prove this
statement. The converse, for a category already equivalent to a module
category, and the construction and comparison of Renard's nonunital
module categories remain separate whole-book obligations. This file
asserts only the forward theorem above.
