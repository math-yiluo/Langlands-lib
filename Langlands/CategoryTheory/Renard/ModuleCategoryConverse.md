# Renard A.VIII.2: the module-category converse, proof

Author: Worker 937 (this module, its helper theorem and this Markdown). It reuses published Library results only by Lean name; see "Source and provenance".

This module proves the published proposition `Langlands.Renard.ModuleCategoryConverseStatement.{w, v, u, r, s} C R` from `Langlands.CategoryTheory.Renard.ModuleCategoryConverseStatements`. The theorem is

```lean
theorem Langlands.Renard.moduleCategoryConverse
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R : Type r) [Ring R] :
    ModuleCategoryConverseStatement.{w, v, u, r, s} C R
```

Unfolded, it says the following. Let `C` be an abelian category with coproducts indexed by every `I : Type w`, and let `R` be any unital ring. Then for every equivalence `e : C ≌ ModuleCat.{max r s} R`,

```lean
HomSmallProgenerator.{w} (e.inverse.obj (ModuleCat.of R (ULift.{s} R)))
```

The object is the actual inverse image under `e` of the left regular module `R`, lifted to the carrier universe `max r s` with `ULift.{s} R`. The predicate is the published one in `C`: exactness, preservation of `w`-indexed coproducts and faithfulness of the integer-module Hom functor `C ⥤ ModuleCat.{v} ℤ` out of that object.

The five universes are independent: `w` (coproduct index size), `v` and `u` (Hom and objects of `C`), `r` (the ring) and `s` (the lift). The ring may be noncommutative or the zero ring. The only coproduct hypothesis is `HasCoproducts.{w} C`. The theorem adds no hypothesis: no coproducts on the module category, no relation between `w` and `max r s`, no generator, enough projectives, Grothendieck or finite-type condition. The statement pair and the pairs it imports are used unchanged.

## Files in this contribution

- `Langlands/CategoryTheory/Renard/ModuleCategoryConverse.lean` and this Markdown: new. No other file is added or edited.

## Helper theorem

In namespace `Langlands.Renard`, public:

```lean
theorem hasCoproducts_moduleCat_of_equivalence
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] {R : Type r} [Ring R]
    (e : C ≌ ModuleCat.{max r s} R) : HasCoproducts.{w} (ModuleCat.{max r s} R)
```

It does not need `C` to be abelian. `HasCoproducts.{w}` means `HasColimitsOfShape (Discrete J)` for every `J : Type w`. For each such `J`, Mathlib's `Adjunction.hasColimitsOfShape_of_equivalence` applied to the functor `e.inverse : ModuleCat.{max r s} R ⥤ C` gives the instance. That functor is an equivalence by Mathlib's instance `Equivalence.isEquivalence_inverse`, and `C` has colimits of shape `Discrete J` by hypothesis. Mathlib's argument: for a diagram `K` in the module category, `K ⋙ e.inverse` has a colimit in `C`; the quasi-inverse preserves it, and the unit isomorphism identifies its image with `K`.

Mathlib's own colimit instances for `ModuleCat.{max r s} R` (`ModuleCat.hasColimitsOfSize`, through the colimits of `AddCommGrpCat`) cover only index types that are small relative to the carrier universe, so for an arbitrary `w` no instance is available without `e`. The helper supplies coproducts of size `w` from the coproducts of `C` and the equivalence. It does not bound `w` by the carrier universe.

## Main proof

Fix `e : C ≌ ModuleCat.{max r s} R`, and write `P = ModuleCat.of R (ULift.{s} R)`.

1. **Coproducts in the module category.** `hasCoproducts_moduleCat_of_equivalence e` gives a local instance `HasCoproducts.{w} (ModuleCat.{max r s} R)`, derived from `e` as above.
2. **The regular module.** With that instance, the published theorem `regularModuleSmallProgenerator.{w, s, r} R` (module `Langlands.CategoryTheory.Renard.RegularModuleSmallProgenerator`) gives `RegularModuleSmallProgeneratorStatement.{w, s, r} R`. That is, by definition, `HomSmallProgenerator.{w} P` in the module category. The theorem takes the `HasCoproducts.{w}` instance as an argument and bounds no universe, so it applies at the arbitrary size `w`.
3. **Back to `C`.** The published theorem `smallProgeneratorTransport.{w} (ModuleCat.{max r s} R) C` (module `Langlands.CategoryTheory.Renard.SmallProgeneratorTransport`) is applied with source the module category and target `C`. The equivalence is the inverse `e.symm : ModuleCat.{max r s} R ≌ C` and the object is `P`. Its source instances are Mathlib's `ModuleCat.abelian` and the derived instance of step 1; its target instances are the hypotheses on `C`. Its forward implication sends `HomSmallProgenerator.{w} P` to `HomSmallProgenerator.{w} (e.symm.functor.obj P)`.
4. **The witness.** The functor of `e.symm` is `e.inverse` by the definition of `Equivalence.symm`, so `e.symm.functor.obj P` is definitionally `e.inverse.obj P`. The result of step 3 is therefore the target for `e`.

Both `HasCoproducts.{w}` instances in the module category are the one derived in step 1. `HasCoproducts` is a proposition, so no choice of instance affects the predicates. The transport theorem has independent source and target object and Hom universes, so the target `C` (Hom universe `v`) and the module category (Hom universe `max r s`) are not compared. Only the common index size `w` is shared.

## Imports

- `Langlands.CategoryTheory.Renard.ModuleCategoryConverseStatements`: the unchanged target.
- `Langlands.CategoryTheory.Renard.RegularModuleSmallProgenerator`: `regularModuleSmallProgenerator`.
- `Langlands.CategoryTheory.Renard.SmallProgeneratorTransport`: `smallProgeneratorTransport`.
- Mathlib `CategoryTheory.Adjunction.Limits`: `Adjunction.hasColimitsOfShape_of_equivalence`.

## Source and provenance

The governing original is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, A.VIII.2, printed page 267 / PDF page 273. Registered source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c` (hash checked, page reread for this unit). The theorem on that page says that a cocomplete abelian category with a small progenerator `P` is equivalent to the unital right modules over `End_A(P)`, through `Hom_A(P, •)`. The remark that follows reads: "On a bien sûr la réciproque, puisque un anneau unitaire A est un petit progénérateur de M(A)" (of course the converse holds, since a unital ring `A` is a small progenerator of `M(A)`). The source gives no further proof.

This module follows the remark's argument: the ring is a small progenerator of its module category (the published regular-module theorem), and a category equivalent to it gets a small progenerator by moving that object across the equivalence (the published transport theorem). The source does not discuss the coproduct size or the transport of coproducts. Step 1 makes explicit that the coproducts the predicate needs in the module category come from `C` through the equivalence. The explicit inverse-image witness and the independent universes belong to the published statement's derived realization; see its Markdown. The source uses right modules. The statement uses Mathlib's left modules, and its Markdown explains that right modules are covered by taking `R` to be an opposite ring.

The supplementary older-edition errata `renard-2010-corrections-complements`, PDF pages 18–19 (SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`), were checked when the transport prerequisite was written. They contain no correction to this remark, and the 2026 edition governs.

The route is the one planned in the statement's Markdown: transport coproducts to the module category, use the regular-module theorem, transport the predicate back along `e.symm`. The proof was written for this unit. The two Library theorems and the Mathlib lemma are imported by name. No code was copied from other contributions.

## Checks

Development checks used the approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`) over Library commit `d08b5767dba1139a70ed7ebfc0438a31c2587868`.

- Compilation and inspection (diagnostic `8d25136a-9c5e-49ac-b85b-3e3540b586f9`): `moduleCategoryConverse` is a theorem with level parameters `w, v, u, r, s`, whose only axioms are `propext`, `Classical.choice` and `Quot.sound`. The only diagnostic was a style hint preferring `have` to `haveI`, which was then applied.
- Private probe (diagnostic `2f4661b0-7d5b-40dd-8073-3ebd3676654a`, no errors or warnings):
  - checked by `rfl` that the type of `@moduleCategoryConverse.{w, v, u, r, s}` is `∀ (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : Type r) [Ring R], ModuleCategoryConverseStatement.{w, v, u, r, s} C R`;
  - elaborated `moduleCategoryConverse C R` against the unfolded statement for every `e`;
  - instantiated the theorem at `(w, v, u, r, s) = (5, 1, 3, 0, 2)` and `(0, 2, 4, 6, 1)`, the first with an index universe above the carrier universe;
  - instantiated it for the zero ring `PUnit` and for the noncommutative ring `Matrix (Fin 2) (Fin 2) ℚ`;
  - derived `∃ P : C, HomSmallProgenerator.{w} P` from any supplied equivalence.
- Workspace recheck (diagnostic `9e99cd2f-e5ce-4ffa-904b-101f46ea6541`): the submitted Lean file built in the workspace with no errors or warnings, with the same level parameters and axioms. It differs from the probed file only in the helper's docstring, which no longer calls `C` abelian.

These are development checks. They do not establish exact-target validation, independent acceptance or publication.

## Scope

This unit proves only the converse for unital left module categories, realized by the inverse regular module. The regular-module theorem, the transport theorem and the forward Hom-equivalence theorem keep their own declarations and authors. Nonunital module categories are not treated here.
