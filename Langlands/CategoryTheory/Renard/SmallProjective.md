# Renard A.VIII.2: small projectives and small progenerators

Authors: Worker 6 (original shared draft, implementation and documentation),
Worker 937 (independent source rereading, declaration inspection and
submission).

This definition unit supplies three predicates and their short unfolding
laws in namespace `Langlands.Renard`, module
`Langlands.CategoryTheory.Renard.SmallProjective`.

## Original source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, A.VIII.2, printed page 267 /
PDF page 273. The actual Hom functors and the additive, abelian setting
start on printed page 266 / PDF page 272. Both complete pages were read.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Renard first fixes a cocomplete abelian category. A projective object `P`
is called small when `Hom(P, •)` preserves direct sums. His following
equivalence theorem assumes a small progenerator. `HomSmallProjective`
formalizes the first definition, and `HomSmallProgenerator` bundles that
small-projective condition with the previously defined generator condition.
`HomPreservesCoproducts` is an internal helper naming the preservation
condition alone; it does not require projectivity.

The supplementary author errata for the 2010 edition,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were reread at their appendix entries on PDF pages 18–19. The entry for
printed page 309, line 2 of the 2010 edition, on errata PDF page 18,
replaces the old fixed object `X` by `P` in the smallness definition:
“si le foncteur Hom_A(P,•) préserve les sommes directes”. The governing
2026 edition already incorporates this correction. These errata are
supplementary evidence and do not replace the governing edition.

## Actual Hom and size parameters

The common setting is

```lean
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]
```

Each predicate and each unfolding law additionally has an explicit binder
`[HasCoproducts.{w} C]` and an object argument `(P : C)`. The coproduct
indexing universe `w`, Hom universe `v` and object universe `u` remain
independent. No equality or ordering among them is imposed.

Source cocompleteness supplies coproducts at the chosen indexing size.
The unit retains precisely their existence, `HasCoproducts.{w} C`, rather
than imposing all colimits on `C`. In Mathlib this abbreviation means
`∀ I : Type w, HasColimitsOfShape (Discrete I) C`. A categorical coproduct
is a colimit over a discrete category; these are the source's direct
sums. The explicit instance binder on each declaration retains the
existence hypothesis even though the preservation predicate can itself
be formulated without it.

Renard's direct sums are indexed by arbitrary sets. The Lean predicates
test every index type in the one chosen universe `w`; instantiating `w`
selects the size of the coproducts that are tested. Taking a different
`w` gives a possibly different condition, and no comparison between the
conditions at different sizes, or between `w` and `v` or `u`, is asserted.

The imported actual functor, in namespace
`Langlands.CategoryTheory.Renard`, is

```lean
preadditiveCoyonedaInt (P : C) : C ⥤ ModuleCat.{v} ℤ
```

Its value at `X` has carrier `P ⟶ X`, with the canonical integer-module
structure of that additive Hom group. For `g : X ⟶ Y`, its map sends
`f : P ⟶ X` to `f ≫ g`. This is the published restriction of scalars of
Mathlib's right endomorphism-module Hom functor. The construction and
its intrinsic laws, authored by Worker 734, are imported from
`Langlands.CategoryTheory.Renard.HomFunctors`.

`HomProjective P`, imported from
`Langlands.CategoryTheory.Renard.HomObjectProperties`, is the source's
sequence exactness of this actual functor. It tests both one-sided exact
sequences, without restricting their inputs to short exact sequences.
`HomGenerator P` is faithfulness of the same actual functor on every
Hom type. These published properties are reused unchanged.

## Exact definitions

With the common binders above, the three predicates are:

```lean
def HomPreservesCoproducts [HasCoproducts.{w} C] (P : C) : Prop :=
  ∀ I : Type w,
    PreservesColimitsOfShape (Discrete I)
      (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P)

def HomSmallProjective [HasCoproducts.{w} C] (P : C) : Prop :=
  HomProjective P ∧ HomPreservesCoproducts.{w} P

def HomSmallProgenerator [HasCoproducts.{w} C] (P : C) : Prop :=
  HomSmallProjective.{w} P ∧ HomGenerator P
```

Here `PreservesColimitsOfShape` is Mathlib's native predicate: for every
diagram `K : Discrete I ⥤ C` and every colimit cocone `c` on `K`, the
mapped cocone of the actual Hom functor is colimiting. Thus the definition
tests all actual discrete diagrams at size `w`, including arbitrary
families of objects of `C`. It asserts preservation of coproducts, not
preservation of arbitrary colimits.

There is no assumption that the target `ModuleCat.{v} ℤ` has all coproducts
at the unrelated size `w`. Preservation is expressed directly by the
universal property of the mapped cocone and needs no target-wide
cocompleteness. The source coproducts do exist by the explicit instance
parameter.

The native definitions were read in prepared Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`:
`Mathlib.CategoryTheory.Limits.Shapes.Products` supplies `HasCoproducts`
and coproducts as discrete colimits;
`Mathlib.CategoryTheory.Limits.Preserves.Basic` supplies
`PreservesColimitsOfShape` and `PreservesColimit`.

## Intrinsic laws and scope

In the same common setting, the complete law statements are:

```lean
homPreservesCoproducts_iff [HasCoproducts.{w} C] (P : C) :
  HomPreservesCoproducts.{w} P ↔
    ∀ I : Type w,
      PreservesColimitsOfShape (Discrete I)
        (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P)

homSmallProjective_iff [HasCoproducts.{w} C] (P : C) :
  HomSmallProjective.{w} P ↔
    HomProjective P ∧ HomPreservesCoproducts.{w} P

homSmallProgenerator_iff [HasCoproducts.{w} C] (P : C) :
  HomSmallProgenerator.{w} P ↔
    HomSmallProjective.{w} P ∧ HomGenerator P
```

Each proof is `Iff.rfl`, exposing its definition. No projectivity,
smallness, generation or preservation conclusion is assumed in the
ambient context, and no global instance for such a property is installed.
All three predicates return `Prop`.

The module compiles without warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Inspection of the six complete
unapplied declarations shows the universe parameters `w, v, u` in that
order, the binders `{C : Type u}`, `[Category.{v, u} C]`,
`[Abelian.{v, u} C]` and `[HasCoproducts.{w, v, u} C]` on each one, and
the axioms `propext`, `Classical.choice` and `Quot.sound` only. Mathlib's
`HasCoproducts.{w, v, u} C` unfolds to
`∀ J : Type w, HasColimitsOfShape (Discrete J) C`.

The finite-support characterization, the finite-type comparison in a
Grothendieck category, presentations by sums of copies of a progenerator,
the regular-module converse and the actual equivalence with right
modules over `End P` remain separate statement and proof obligations.
This unit supplies none of those theorems and assumes none of them.
