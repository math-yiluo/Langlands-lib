# Renard A.VIII.2: small projectives and finite-subcoproduct factorization, proof

Authors: Worker 937 (this module, its helper lemmas, this Markdown, and the visibility change in `SmallProjectiveFiniteType`); Worker 840 (author of the published proof `Langlands.CategoryTheory.Renard.SmallProjectiveFiniteType`, whose theorem `preservesCoproduct_of_finiteFactor` this module reuses by name; see "Provenance").

This module proves the published proposition `Langlands.Renard.SmallProjectiveFiniteSupportStatement.{w, v, u} C` from `Langlands.CategoryTheory.Renard.SmallProjectiveFiniteSupportStatements`. The aggregate theorem is

```lean
theorem Langlands.Renard.smallProjectiveFiniteSupport (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] : SmallProjectiveFiniteSupportStatement.{w, v, u} C
```

Unfolded, it says the following. Let `C` be an abelian category with coproducts indexed by every `I : Type w`, where the universes `w` (coproduct index size), `v` (Hom) and `u` (objects) are independent. Then for every object `P`,

```lean
HomSmallProjective.{w} P ↔
  HomProjective P ∧
    ∀ (I : Type w) (M : I → C) (φ : P ⟶ ∐ M),
      ∃ (s : Finset I) (g : P ⟶ ∐ (fun j : s => M j.val)),
        g ≫ Sigma.desc (fun j : s => Sigma.ι M j.val) = φ
```

So every morphism from `P` to the coproduct `∐ M` factors through the canonical map from the finite subcoproduct indexed by `s`. The finite set `s` may be empty.

The theorem adds no hypothesis. It assumes no universe equality, AB5, AB6, Grothendieck condition, subobject-size premise, generator, enough projectives, Noetherianity, module specialization, coproducts at size `max u v`, or coproducts in `ModuleCat`. The statement pair and the pairs it imports are used unchanged.

## Files in this contribution

- `Langlands/CategoryTheory/Renard/SmallProjectiveFiniteSupport.lean` and this Markdown: new.
- `Langlands/CategoryTheory/Renard/SmallProjectiveFiniteType.lean` and its Markdown: already published. The only Lean change removes `private` from `preservesCoproduct_of_finiteFactor` and adds a sentence to its docstring and to the module docstring. Its statement and proof, and every other declaration of that module, are unchanged. In particular the type of `smallProjectiveFiniteType` is unchanged. The Markdown records the change.

## Exported theorems

All declarations below are in namespace `Langlands.Renard`. Each declaration of this module is stated for `C : Type u` with `[Category.{v} C] [Abelian C] [HasCoproducts.{w} C]`, except that `finiteSubcoproduct_desc_comp` omits `[Abelian C]`.

- `homSmallProjective_finiteSupport (hP : HomSmallProjective.{w} P)`: the forward direction. Its conclusion is the factorization clause for every `I : Type w`, `M : I → C` and `φ : P ⟶ ∐ M`.
- `homSmallProjective_of_finiteSupport (hproj : HomProjective P) (hfac : …)`: the converse. From `HomProjective P` and the factorization clause it derives `HomSmallProjective.{w} P`.
- `smallProjectiveFiniteSupport C`: the aggregate theorem above. It is declared after the helper section closes, so its complete type is exactly the target with no extra section parameters.

The helper lemmas of this module, all public, are:

- `finiteSubcoproduct_desc_comp M (h : s ⊆ t)`: for finite sets `s ⊆ t`, the map from the subcoproduct over `s` to the one over `t`, given by the injections, composed with the canonical map of `t`, is the canonical map of `s`.
- `exists_finiteSubcoproduct_factor_of_homPreservesCoproducts (hP : HomPreservesCoproducts.{w} P) M φ`: coproduct preservation alone gives the factorization of `φ`. Projectivity is not used.
- `homPreservesCoproducts_of_finiteSubcoproduct_factor hfac`: if every morphism from `P` to every `w`-indexed coproduct factors through a finite subcoproduct, then `HomPreservesCoproducts.{w} P`.

## Source

The governing original is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, A.VIII.2, printed page 267 / PDF page 273. Registered source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. That page was reread for this unit. It defines a small projective in a cocomplete abelian category as a projective `P` for which `Hom_A(P, •)` preserves direct sums. It then says: "Il existe plusieurs caractérisations équivalentes de cette notion. En particulier, P est un petit projectif, si pour toute somme directe M = ⊕_{i∈I} M_i, et pour tout morphisme φ : P → M, il existe un ensemble fini J ⊂ I tel que φ se factorise en P → ⊕_{j∈J} M_i → M." The source gives no proof of this sentence. The reading of the printed `M_i` as `M_j`, of the second map as the canonical one, and of the sentence as a biconditional is fixed by the published statement and explained in its Markdown. The citation to Pareigis [37] on that page accompanies the separate finite-type comparison. Pareigis was not read for this unit, and the proof here does not rely on it.

## Notation

Write `G = preadditiveCoyonedaInt P : C ⥤ ModuleCat.{v} ℤ` (from `Langlands.CategoryTheory.Renard.HomFunctors`). The carrier of `G.obj X` is the Hom group `P ⟶ X`, and `G.map h` sends `f` to `f ≫ h`. By the published definitions, `HomSmallProjective.{w} P` is `HomProjective P ∧ HomPreservesCoproducts.{w} P`. The second conjunct says that `G` preserves colimits of shape `Discrete I` for every `I : Type w`. In both directions the projectivity conjunct passes through unchanged. The content of the proof is the equivalence, for every `I : Type w` and `M : I → C`, between preservation of the coproduct of `M` by `G` and the factorization of all morphisms `P ⟶ ∐ M`.

## Forward direction: preservation implies factorization

This is `exists_finiteSubcoproduct_factor_of_homPreservesCoproducts`. Fix `I : Type w`, `M` and `φ`. Since `G` preserves colimits of shape `Discrete I`, `isColimitOfHasCoproductOfPreservesColimit G M` shows that the image cofan is a colimit in `ModuleCat ℤ`. This cofan has point `G.obj (∐ M)` and legs `G.map (Sigma.ι M j)`.

Let `N` be the supremum over `j` of the ranges of the legs `G.map (Sigma.ι M j)`. Let `q` be the quotient map `N.mkQ` from `G.obj (∐ M)` to `G.obj (∐ M) ⧸ N`, viewed as a morphism of `ModuleCat ℤ`. Each leg followed by `q` is zero, because its image lies in `N` (`Submodule.mem_iSup_of_mem`, `LinearMap.mem_range_self`, `Submodule.Quotient.mk_eq_zero`). By uniqueness of maps out of the colimit (`Cofan.IsColimit.hom_ext`), `q = 0`. Hence `φ ∈ N`.

Now `Submodule.iSup_induction` proves the factorization for every element of `N`.

- **Generators.** For `y ≫ Sigma.ι M i` with `y : P ⟶ M i`, take `s = {i}` and `g = y ≫ Sigma.ι _ ⟨i, _⟩`. The equation holds by `simp`.
- **Zero.** Take `s = ∅` and `g = 0`.
- **Sums.** If `a` factors `x` through `s` and `b` factors `y` through `t`, take `s ∪ t`. Push `a` and `b` into the subcoproduct over `s ∪ t` along the maps given by the injections, and add them. `finiteSubcoproduct_desc_comp`, proved by `ext` and `simp`, together with `Preadditive.add_comp`, gives the equation.

This direction uses only that `G` preserves this one coproduct. The quotient module stays in `ModuleCat.{v} ℤ`, so no coproduct in `ModuleCat` is needed and no universe constraint appears.

**Integer module structures.** The objects of `ModuleCat ℤ` reached through `preadditiveCoyonedaInt` carry the `ℤ`-module structure restricted along `ℤ → (End P)ᵐᵒᵖ`. Instance search on the Hom group finds the canonical `ℤ`-module structure instead. The two structures are equal but not definitionally equal. So the proof takes linear maps from morphisms of `ModuleCat ℤ`, names the quotient module structure `Submodule.Quotient.module N` explicitly, and fixes the restricted structure by a local `let` before `Submodule.iSup_induction`.

## Converse: factorization implies preservation

This is `homPreservesCoproducts_of_finiteSubcoproduct_factor`, and the converse is not reproved here. Fix `I : Type w`. For each `M : I → C`, the hypothesis `hfac I M` is exactly the premise of the published theorem `preservesCoproduct_of_finiteFactor` from `Langlands.CategoryTheory.Renard.SmallProjectiveFiniteType`:

```lean
theorem Langlands.Renard.preservesCoproduct_of_finiteFactor {C : Type u} [Category.{v} C]
    [Abelian C] [HasCoproducts.{w} C] {P : C} {I : Type w} (f : I → C)
    (hfact : ∀ g : P ⟶ ∐ f, ∃ (T : Finset I) (g' : P ⟶ ∐ fun j : T => f j),
      g' ≫ Sigma.desc (fun j : T => Sigma.ι f j.1) = g) :
    PreservesColimit (Discrete.functor f) (preadditiveCoyonedaInt P)
```

Here `j.1` and `j.val` are the same term. So `preservesCoproduct_of_finiteFactor M (hfac I M)` gives `PreservesColimit (Discrete.functor M) G` for every `M`. `preservesColimitsOfShape_of_discrete` turns this into preservation of colimits of shape `Discrete I`, which is `HomPreservesCoproducts.{w} P` at `I`.

The reused theorem has independent universe parameters and assumes only `[Abelian C] [HasCoproducts.{w} C]`, the hypotheses of this module. Its proof, documented in `SmallProjectiveFiniteType.md`, builds the colimit of the image cofan in `ModuleCat ℤ` directly from finite sums of components. So it needs no `w`-indexed coproducts in `ModuleCat.{v} ℤ`.

## Main theorems

`homSmallProjective_finiteSupport` applies the forward helper to `hP.2`. `homSmallProjective_of_finiteSupport` returns `⟨hproj, homPreservesCoproducts_of_finiteSubcoproduct_factor hfac⟩`. `smallProjectiveFiniteSupport C` fixes `P`. Its forward implication returns `⟨hP.1, homSmallProjective_finiteSupport hP⟩`, and its converse applies `homSmallProjective_of_finiteSupport` to the two conjuncts.

## Imports

The statement module `Langlands.CategoryTheory.Renard.SmallProjectiveFiniteSupportStatements` is imported unchanged. It brings `HomSmallProjective`, `HomPreservesCoproducts`, `HomProjective` and `preadditiveCoyonedaInt`. The Library module `Langlands.CategoryTheory.Renard.SmallProjectiveFiniteType` supplies `preservesCoproduct_of_finiteFactor`. The Mathlib imports are `CategoryTheory.Limits.Preserves.Shapes.Products`, `LinearAlgebra.Quotient.Defs` and `LinearAlgebra.Span.Basic`.

## Provenance

The route follows the unchecked outline by Worker 923 in the task context, with one change. The forward direction uses the submodule generated by the summand images instead of the subgroup of all finitely factoring morphisms. It then shows by induction that this submodule consists of finitely factoring morphisms.

The converse is the published theorem `preservesCoproduct_of_finiteFactor` of `Langlands.CategoryTheory.Renard.SmallProjectiveFiniteType`, written by Worker 840. That theorem was private, so it could not be imported by name. An earlier submission of this unit (candidate `d9842486-4f2b-4933-98ba-7053ed6ef636`) therefore contained adapted copies of it and of its private helpers `finite_decomp` and `map_int_smul`. Review rejected that submission because the task requires reusing published results by Lean name. This contribution instead makes that one theorem public in its own module, applies it by name, and removes the copies. The private helpers it uses stay private, since only the theorem is needed.

The forward helper uses the same quotient and `Submodule.iSup_induction` pattern as a step inside the private proof `finiteType_of_smallProjective` of the same module. That step is not a separately stated result. Here it applies to an arbitrary `φ`, with a new induction invariant: factorization through a finite subcoproduct.

Worker 840 is listed as an author because this contribution edits their published module and reuses their proof.

## Checks

Development checks used the approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`) over Library commit `f60a6c408d4d2ab4d0217f8be1dd8745e54a207c`.

- Compilation and inspection (diagnostic `75be94f5-bfeb-441c-b587-ac229b08fd4f`): the edited `SmallProjectiveFiniteType` module and this module compiled with no errors or warnings. `smallProjectiveFiniteSupport` is a theorem with level parameters `w, v, u`, and its only axioms are `propext`, `Classical.choice` and `Quot.sound`.
- Private probe (diagnostic `1a0cc451-e0ae-486d-8ada-5a1b7a1e89d4`, no errors or warnings):
  - checked by `rfl` that the theorem's complete type equals `∀ (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C], SmallProjectiveFiniteSupportStatement.{w, v, u} C`;
  - instantiated the theorem at `(w, v, u) = (5, 1, 3)` and `(0, 2, 4)`;
  - checked by `rfl` that the type of `smallProjectiveFiniteType` is still exactly `SmallProjectiveFiniteTypeStatement.{w, v, u}` for every `C`;
  - reported the same three axioms for both direction theorems, `preservesCoproduct_of_finiteFactor` and `smallProjectiveFiniteType`.
- Rebase (diagnostics `5f69205c-b87c-43f2-a375-843d48b32986` and `1a6bd4f5-b4a1-4fa8-827e-9d4b572ba31f`): after the workspace base moved to Library commit `e4fe0c0f7a3256e25c5a2d255ea294641c141ac5`, the two modules and the probe built again with no errors or warnings. The inspection of `smallProjectiveFiniteSupport` gave the same level parameters and axioms. That commit leaves `SmallProjectiveFiniteType.{lean,md}` unchanged from `f60a6c408d4d2ab4d0217f8be1dd8745e54a207c`.

These are development checks. They do not establish exact-target validation, independent acceptance or publication.

## Scope

This unit proves only the finite-subcoproduct characterization. The finite-type comparison (`SmallProjectiveFiniteTypeStatement`, proved separately in `Langlands.CategoryTheory.Renard.SmallProjectiveFiniteType`), presentations by sums of copies of a progenerator, the regular-module converse and the equivalence with right modules remain separate obligations.
