# Renard A.VI.2(10): proof that complete abelian categories have all limits

Author: Worker 800 (Lean proof and this note). The proved statement and its
specification are the published unit
`Langlands.CategoryTheory.RenardCompletenessLimitsStatements`, by Worker 800
and Worker 6. This unit imports that module by name and does not change it.
The proof route is the one Worker 800 checked earlier in a private
type-feasibility diagnostic; no other draft was reused.

## Target

Module `Langlands.CategoryTheory.RenardCompletenessLimits` proves

```lean
theorem Langlands.Renard.sourceCompletenessLimits.{w, v, u}
    (C : Type u) [Category.{v} C] [Abelian C] :
    SourceCompletenessLimitsStatement.{w} C
```

for an arbitrary abelian category `C`, with independent family size `w`, Hom
universe `v` and object universe `u`. The universe parameters are in the order
`w, v, u` of the statement, and the binders `(C : Type u) [Category.{v} C]
[Abelian C]` appear in the statement's order, with no further section
parameters. No hypothesis is added: no `WellPowered`, `LocallySmall`,
generator, separator, exactness, smallness or filteredness condition, and no
use of Mathlib's `IsGrothendieckAbelian`, `AB4OfSize` or `AB4StarOfSize`.

By the statement unit, `SourceCompletenessLimitsStatement.{w} C` is the
conjunction of

- `SourceCompleteHasLimitsStatement.{w} C`, that is
  `IsSourceComplete.{w} C → HasLimitsOfSize.{w, w} C`, and
- `SourceCocompleteHasColimitsStatement.{w} C`, that is
  `IsSourceCocomplete.{w} C → HasColimitsOfSize.{w, w} C`,

where the source predicates of `Langlands.CategoryTheory.RenardGrothendieckAxioms`
are transparent abbreviations of `HasProducts.{w} C` and `HasCoproducts.{w} C`.
The conclusions say that every functor `F : J ⥤ C` with `J : Type w` and
`Category.{w} J` has a limit (resp. a colimit).

The original assertion is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, Appendix A.VI.2(10), printed
page 263 / PDF page 269 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). The
source states (10) without proof. The proof below is the standard
construction, implemented by Mathlib, and does not follow a route from the
source.

## Proof method

Two facts combine.

1. *Equalizers and coequalizers.* Every abelian category has them, through
   Mathlib's instances `CategoryTheory.Abelian.hasEqualizers` and
   `CategoryTheory.Abelian.hasCoequalizers`
   (`Mathlib/CategoryTheory/Abelian/Basic.lean`). They are
   `Preadditive.hasEqualizers_of_hasKernels` and
   `Preadditive.hasCoequalizers_of_hasCokernels`: the equalizer of `f, g` is
   the kernel of `f - g`, and the coequalizer is the cokernel of `f - g`.
2. *Limits from products and equalizers.* Mathlib's
   `CategoryTheory.Limits.has_limits_of_hasEqualizers_and_products`
   (`Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean`)
   states that `[HasProducts.{w} C] [HasEqualizers C]` give
   `HasLimitsOfSize.{w, w} C`. For `F : J ⥤ C` with `J : Type w` and
   `Category.{w} J`, the limit is built (`limitConeOfEqualizerAndProduct`) as
   the equalizer of two maps
   `∏ᶜ F.obj ⟶ ∏ᶜ (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)`: on the
   factor indexed by an arrow `f : i ⟶ j`, one map is the projection to
   `F.obj i` followed by `F.map f` and the other is the projection to
   `F.obj j`. Both index types, `J` and `Σ p : J × J, p.1 ⟶ p.2`, lie in
   `Type w`, because the objects and the morphisms of `J` do, so the products
   exist by `HasProducts.{w} C`. Dually,
   `CategoryTheory.Limits.has_colimits_of_hasCoequalizers_and_coproducts`
   states that `[HasCoproducts.{w} C] [HasCoequalizers C]` give
   `HasColimitsOfSize.{w, w} C`, with the colimit built as the coequalizer of
   two maps between the analogous coproducts.

## Declarations

All three theorems are in namespace `Langlands.Renard` and take `C`
explicitly, through `variable (C : Type u) [Category.{v} C] [Abelian C]`.

- `sourceCompleteHasLimits C : SourceCompleteHasLimitsStatement.{w} C`. The
  proof takes `h : IsSourceComplete.{w} C`, records it as a local instance
  `have : HasProducts.{w} C := h` (accepted by definitional unfolding of the
  abbreviation), and closes the goal `HasLimitsOfSize.{w, w} C` with
  `has_limits_of_hasEqualizers_and_products`. Its equalizer argument is found
  by instance search from `Abelian C`.
- `sourceCocompleteHasColimits C : SourceCocompleteHasColimitsStatement.{w} C`.
  Dually, from `h : IsSourceCocomplete.{w} C` it records
  `have : HasCoproducts.{w} C := h` and applies
  `has_colimits_of_hasCoequalizers_and_coproducts`, with coequalizers from
  `Abelian C`.
- `sourceCompletenessLimits C : SourceCompletenessLimitsStatement.{w} C`, the
  aggregate, is the pair
  `⟨sourceCompleteHasLimits.{w} C, sourceCocompleteHasColimits.{w} C⟩`.

The two halves are separately reusable for the two published halves of the
statement.

## Checks and scope

The module imports `Langlands.CategoryTheory.RenardCompletenessLimitsStatements`
and `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers`.
A `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` built it
with no errors and no warnings. Its inspection reported each of
`Langlands.Renard.sourceCompletenessLimits`, `sourceCompleteHasLimits` and
`sourceCocompleteHasColimits` as a theorem with level parameters `w, v, u`
and axioms exactly `propext`, `Classical.choice` and `Quot.sound`.
The file contains no `sorry`, `admit` or new axioms and does not assume its
conclusion.

The result is limited to the fixed size `w`: it gives limits and colimits of
diagrams whose index category has objects and morphisms in `Type w`, and
nothing for larger diagrams or for all universes at once. Smaller index
categories, such as `WalkingParallelPair : Type`, are reached through
Mathlib's `hasLimitsOfSizeShrink` and `hasColimitsOfSizeShrink`, as the
statement note explains. The inverse and direct systems of the source's last
sentence are particular cases, as explained there. The existence of sums of
arbitrary families of subobjects, the comparisons with Mathlib's AB5 and
Grothendieck classes, and the AB6 assertions of A.VI.3 are separate
obligations, not proved here.
