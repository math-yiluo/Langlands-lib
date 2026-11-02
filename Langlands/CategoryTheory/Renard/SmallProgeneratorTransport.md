# Transport of Renard's small progenerators across equivalences, proof

Author: Worker 937 (this module, its helper lemmas and this Markdown). It reuses published Library results only by Lean name; see "Provenance".

This module proves the published proposition `Langlands.Renard.SmallProgeneratorTransportStatement.{w, v, u, v', u'} C D` from `Langlands.CategoryTheory.Renard.SmallProgeneratorTransportStatements`. The theorem is

```lean
theorem Langlands.Renard.smallProgeneratorTransport
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (D : Type u') [Category.{v'} D] [Abelian D] [HasCoproducts.{w} D] :
    SmallProgeneratorTransportStatement.{w, v, u, v', u'} C D
```

Unfolded, it says the following. Let `C` and `D` be abelian categories, each with coproducts indexed by every `I : Type w`. The five universes `w` (common coproduct index size), `v` and `u` (Hom and objects of `C`), and `v'` and `u'` (Hom and objects of `D`) are independent. Then for every equivalence `e : C ≌ D` and every object `P : C`,

```lean
HomSmallProgenerator.{w} P ↔ HomSmallProgenerator.{w} (e.functor.obj P)
```

Both sides use the same index size `w`. The left side concerns the Hom functor `C ⥤ ModuleCat.{v} ℤ` and the right side the Hom functor `D ⥤ ModuleCat.{v'} ℤ`. The proof never compares these two module categories.

The theorem adds no hypothesis. It assumes nothing about the equivalence beyond its being an actual `C ≌ D`: no additivity, exactness, preservation of the Hom coproducts, projectivity or generation is supplied. It assumes no relation between the universes, no finite-length condition, no module equivalence and no coproducts at a maximal universe. The statement pair and the pairs it imports are used unchanged.

## Files in this contribution

- `Langlands/CategoryTheory/Renard/SmallProgeneratorTransport.lean` and this Markdown: new. No other file is added or edited.

## The predicates

Write `G_P = preadditiveCoyonedaInt P : C ⥤ ModuleCat.{v} ℤ` (from `Langlands.CategoryTheory.Renard.HomFunctors`). The carrier of `G_P.obj X` is the Hom group `P ⟶ X`, and `G_P.map h` sends `f` to `f ≫ h`. By the published definitions in `Langlands.CategoryTheory.Renard.HomObjectProperties` and `Langlands.CategoryTheory.Renard.SmallProjective`:

- `HomProjective P` is `SequenceExact G_P`;
- `HomPreservesCoproducts.{w} P` says that `G_P` preserves colimits of shape `Discrete I` for every `I : Type w`;
- `HomGenerator P` is `G_P.Faithful`;
- `HomSmallProgenerator.{w} P` is `(HomProjective P ∧ HomPreservesCoproducts.{w} P) ∧ HomGenerator P`, the inner conjunction being `HomSmallProjective.{w} P`.

The proof transports each of the three conjuncts separately.

## Helper lemmas

All declarations below are in namespace `Langlands.Renard` and are public. The helpers are stated for `C : Type u` with `[Category.{v} C] [Abelian C]` and, where needed, `D : Type u'` with `[Category.{v'} D] [Abelian D]`. Lemmas about coproducts also assume `[HasCoproducts.{w} C]` and, when `D` occurs, `[HasCoproducts.{w} D]`. The exception is `sigmaComparison_map_finiteSubcoproduct_desc`, which drops `[Abelian C] [Abelian D]`.

- `homGenerator_iff_cancel P`: `HomGenerator P` holds iff for all parallel `f g : X ⟶ Y`, if `h ≫ f = h ≫ g` for every `h : P ⟶ X`, then `f = g`.
- `homProjective_of_iso`, `homPreservesCoproducts_of_iso`, `homGenerator_of_iso`, `homSmallProgenerator_of_iso`: each predicate passes from `P` to `P'` along an isomorphism `i : P ≅ P'`.
- `sigmaComparison_map_finiteSubcoproduct_desc G N s`: for a functor `G : D ⥤ C`, a family `N : I → D` with `I : Type w` and a finite set `s : Finset I`, the square formed by the coproduct comparison maps of `G` and the canonical maps from the subcoproduct over `s` commutes:

  ```lean
  sigmaComparison G (fun j : s => N j.val) ≫ G.map (Sigma.desc fun j : s => Sigma.ι N j.val) =
    (Sigma.desc fun j : s => Sigma.ι (fun i => G.obj (N i)) j.val) ≫ sigmaComparison G N
  ```

- `homProjective_functor_obj e`, `homPreservesCoproducts_functor_obj e`, `homGenerator_functor_obj e`, `homSmallProgenerator_functor_obj e`: for `e : C ≌ D`, each predicate passes from `P` to `e.functor.obj P`.

The main theorem `smallProgeneratorTransport` is declared after the helper section closes, so its complete type is exactly the target with no extra section parameters.

## Generation by cancellation

`homGenerator_iff_cancel` rewrites faithfulness of `G_P` without mentioning `ModuleCat`. Forward: if `G_P` is faithful and `h ≫ f = h ≫ g` for every `h`, then `G_P.map f` and `G_P.map g` agree elementwise, so they are equal by extensionality, and `Functor.map_injective` gives `f = g`. Backward: if `G_P.map f = G_P.map g`, evaluating at `h` (`ConcreteCategory.congr_hom`) gives `h ≫ f = h ≫ g` for every `h`, so `f = g` by the cancellation hypothesis.

This characterization involves only morphisms of `C`. Every later use of generation goes through it, so generation in `C` and in `D` can be compared even though the two Hom functors land in module categories of different universes.

## Invariance under isomorphism

Fix `i : P ≅ P'`.

- **Projectivity.** The published comparison `homProjectiveComparison` from `Langlands.CategoryTheory.Renard.HomExactnessComparison` gives `HomProjective P ↔ Projective P`, where `Projective` is Mathlib's lifting class. Mathlib's `Projective.of_iso i` moves projectivity from `P` to `P'`, and the comparison at `P'` brings it back.
- **Coproduct preservation.** This uses the two published helpers of `Langlands.CategoryTheory.Renard.SmallProjectiveFiniteSupport`:
  - `exists_finiteSubcoproduct_factor_of_homPreservesCoproducts`: if `HomPreservesCoproducts.{w} P`, then every `φ : P ⟶ ∐ M` with `M : I → C` and `I : Type w` factors as `g ≫ Sigma.desc (fun j : s => Sigma.ι M j.val)` for some finite `s : Finset I`;
  - `homPreservesCoproducts_of_finiteSubcoproduct_factor`: conversely, if every such morphism from `P` factors in this way, then `HomPreservesCoproducts.{w} P`.

  Given `φ : P' ⟶ ∐ M`, factor `i.hom ≫ φ` through `s` by some `g`. Then `i.inv ≫ g` factors `φ`. The second helper concludes.
- **Generation.** By `homGenerator_iff_cancel`, suppose `h ≫ f = h ≫ g` for every `h : P' ⟶ X`. For any `k : P ⟶ X`, apply this to `h = i.inv ≫ k` and precompose with `i.hom`. Since `i.hom ≫ i.inv` is the identity, this gives `k ≫ f = k ≫ g`, and cancellation at `P` gives `f = g`.

`homSmallProgenerator_of_iso` combines the three.

## Transport along an equivalence

Fix `e : C ≌ D` and `P : C`, and let `adj = e.toAdjunction : e.functor ⊣ e.inverse`. Its bijection `adj.homEquiv P Y : (e.functor.obj P ⟶ Y) ≃ (P ⟶ e.inverse.obj Y)` is natural in `Y` (`Adjunction.homEquiv_naturality_right` and `Adjunction.homEquiv_naturality_right_symm`).

- **Projectivity.** `homProjective_functor_obj` rewrites both sides with `homProjectiveComparison`, at `P` in `C` and at `e.functor.obj P` in `D`, and applies Mathlib's `Equivalence.map_projective_iff e P : Projective (e.functor.obj P) ↔ Projective P`.

- **Coproduct preservation.** This is `homPreservesCoproducts_functor_obj`. By `homPreservesCoproducts_of_finiteSubcoproduct_factor` in `D`, it suffices to factor every `ψ : e.functor.obj P ⟶ ∐ N`, where `N : I → D` and `I : Type w`, through a finite subcoproduct. The inverse `e.inverse` is an equivalence, so it preserves all colimits (Mathlib's instance `isEquivalence_preservesColimits`, which has independent universes). Hence its coproduct comparison `σ_N = sigmaComparison e.inverse N : ∐ (fun i => e.inverse.obj (N i)) ⟶ e.inverse.obj (∐ N)` is an isomorphism, found by instance search (`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`). Then:
  1. The morphism `adj.homEquiv _ _ ψ ≫ inv σ_N : P ⟶ ∐ (fun i => e.inverse.obj (N i))` goes into a `w`-indexed coproduct in `C`. `exists_finiteSubcoproduct_factor_of_homPreservesCoproducts` applied to `hP` gives a finite `s` and `g : P ⟶ ∐ (fun j : s => e.inverse.obj (N j.val))` that factor it.
  2. Put `g' = (adj.homEquiv _ _).symm (g ≫ σ_s)`, where `σ_s = sigmaComparison e.inverse (fun j : s => N j.val)`. Then `g'` is a morphism `e.functor.obj P ⟶ ∐ (fun j : s => N j.val)`.
  3. To see `g' ≫ Sigma.desc (fun j : s => Sigma.ι N j.val) = ψ`, apply the injective map `adj.homEquiv _ _`. By naturality the left side becomes `g ≫ σ_s ≫ e.inverse.map (Sigma.desc …)`. `sigmaComparison_map_finiteSubcoproduct_desc` (proved by `ext` and `simp`) turns this into `g ≫ Sigma.desc (…) ≫ σ_N`. The factorization from step 1 turns that into `adj.homEquiv _ _ ψ ≫ inv σ_N ≫ σ_N`, which is `adj.homEquiv _ _ ψ`.

  No functor between the module categories occurs. The comparison uses only morphisms of `C` and `D`, the adjunction bijection and the coproduct comparison of `e.inverse`.

- **Generation.** This is `homGenerator_functor_obj`. By `homGenerator_iff_cancel` in `D`, suppose `f g : X ⟶ Y` in `D` satisfy `h ≫ f = h ≫ g` for every `h : e.functor.obj P ⟶ X`. Since `e.inverse` is faithful, it suffices to show `e.inverse.map f = e.inverse.map g`. By cancellation at `P` in `C`, it suffices that `k ≫ e.inverse.map f = k ≫ e.inverse.map g` for every `k : P ⟶ e.inverse.obj X`. Apply the injective map `(adj.homEquiv _ _).symm`. By naturality the two sides become `(adj.homEquiv _ _).symm k ≫ f` and `(adj.homEquiv _ _).symm k ≫ g`. These are equal by the hypothesis.

`homSmallProgenerator_functor_obj e` combines the three conjuncts.

## Main theorem

`smallProgeneratorTransport C D` takes `e` and `P`.

- **Forward.** This is `homSmallProgenerator_functor_obj e`.
- **Converse.** Suppose `HomSmallProgenerator.{w} (e.functor.obj P)`. The forward helper for the inverse equivalence `e.symm : D ≌ C`, whose functor is `e.inverse`, gives `HomSmallProgenerator.{w} (e.inverse.obj (e.functor.obj P))`. It uses the hypotheses `[HasCoproducts.{w} D]` and `[HasCoproducts.{w} C]` already present. The unit isomorphism gives `(e.unitIso.app P).symm : e.inverse.obj (e.functor.obj P) ≅ P`, and `homSmallProgenerator_of_iso` transports the predicate to `P`.

Both directions concern the same index size `w`, because the same factorization helpers are used in `C` and in `D` with index types in `Type w`.

## Imports

- `Langlands.CategoryTheory.Renard.SmallProgeneratorTransportStatements`: the unchanged target, which brings `HomSmallProgenerator` and the predicates it is built from.
- `Langlands.CategoryTheory.Renard.SmallProjectiveFiniteSupport`: `exists_finiteSubcoproduct_factor_of_homPreservesCoproducts` and `homPreservesCoproducts_of_finiteSubcoproduct_factor`.
- `Langlands.CategoryTheory.Renard.HomExactnessComparison`: `homProjectiveComparison`.
- Mathlib: `CategoryTheory.Adjunction.Limits`, `CategoryTheory.Limits.Preserves.Shapes.Products` and `CategoryTheory.Preadditive.Projective.Basic`.

## Source and provenance

This is a derived prerequisite, not a separately printed result. The governing original is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, A.VIII.2, printed page 267 / PDF page 273. Registered source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. That page was reread for this unit. It defines projective objects and generators through the functor `Hom_A(X, •)`, calls a projective `P` in a cocomplete abelian category small when `Hom_A(P, •)` preserves direct sums, and states the theorem that a cocomplete abelian category with a small progenerator `P` is equivalent to right modules over `End_A(P)`. The remark that follows reads: "On a bien sûr la réciproque, puisque un anneau unitaire A est un petit progénérateur de M(A)".

The source does not state that small progenerators are preserved by equivalences. The remark uses this tacitly: to get a small progenerator of a category equivalent to `M(A)`, one moves the regular module across the equivalence. The published statement makes that step an explicit proposition, and this module proves it. The argument above is not taken from the source, which gives no proof of the remark. It was written for this unit from the published definitions and comparisons.

The supplementary older-edition errata `renard-2010-corrections-complements` (SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`) were reread at PDF pages 18–19. Their correction "p. 309, l. 2 : remplacer X par P : si le foncteur Hom_A(P,•) préserve les sommes directes" fixes the variable in the smallness condition of the 2010 edition. The 2026 page already has `P` there. The errata say nothing about transport along equivalences.

The route follows the plan in the statement's Markdown: projectivity and generation through comparisons with native categorical notions, smallness through factorization through finite subcoproducts. For generation, this module proves its own elementwise cancellation characterization, `homGenerator_iff_cancel`, rather than citing a published generation comparison. All reused results are published Library theorems imported by name. No code was copied from other contributions.

## Checks

Development checks used the approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`) over Library commit `dad4d948ab2f6838277ce9094bcc92df1507b0cb`.

- Compilation and inspection (diagnostic `28f40a81-df23-4f23-b6a2-521208306fba`): the module compiled with no errors or warnings. `smallProgeneratorTransport` is a theorem with level parameters `w, v, u, v', u'`, and its only axioms are `propext`, `Classical.choice` and `Quot.sound`.
- Private probe (diagnostic `ca9a003e-40ac-4f7b-99eb-eb607604eab3`, no errors or warnings):
  - elaborated `@smallProgeneratorTransport.{w, v, u, v', u'}` against the complete type `∀ (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (D : Type u') [Category.{v'} D] [Abelian D] [HasCoproducts.{w} D], SmallProgeneratorTransportStatement.{w, v, u, v', u'} C D`;
  - elaborated `smallProgeneratorTransport C D` against the unfolded biconditional for every `e` and `P`;
  - instantiated the theorem at `(w, v, u, v', u') = (3, 1, 5, 0, 2)` and `(0, 4, 2, 6, 1)`.
- Workspace recheck (diagnostic `af0d2ed6-482f-4722-87da-d915b89f980c`): the submitted Lean file, unchanged, built in the workspace with no errors or warnings, with the same level parameters and axioms.

These are development checks. They do not establish exact-target validation, independent acceptance or publication.

## Scope

This unit proves only the transport biconditional. The realization of the categorical converse of Renard's theorem through the regular module, the regular-module theorem itself, the forward Hom-equivalence theorem and the finite-support and finite-type characterizations remain separate results with their own declarations.
