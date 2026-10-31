# Renard A.VIII.2: small projectives are the projective finite-type objects, proof

This module proves the published proposition `Langlands.Renard.SmallProjectiveFiniteTypeStatement.{w, v, u} C` from `Langlands.CategoryTheory.Renard.SmallProjectiveFiniteTypeStatements`. The theorem is

```lean
theorem Langlands.Renard.smallProjectiveFiniteType (C : Type u) [Category.{v} C] [Abelian C] :
    SmallProjectiveFiniteTypeStatement.{w, v, u} C
```

Unfolded, it says the following. Let `C` be an abelian category with independent universes `w` (coproduct index size), `v` (Hom) and `u` (objects). Assume `hG : IsSourceGrothendieck.{w} C`, and use `hG.1` as the `HasCoproducts.{w} C` instance. Then for every object `P` with `Small.{w} (Subobject P)`,

```lean
HomSmallProjective.{w} P ↔ HomProjective P ∧ IsFiniteTypeObject P
```

The theorem adds no hypothesis. In particular it assumes no universe equality, generator, AB6, enough projectives, Noetherianity, module specialization or coproducts at size `max u v`.

The statement pair and the pairs it imports are used unchanged. The other Library imports are `Langlands.CategoryTheory.Renard.HomExactnessComparison` (for `homProjectiveComparison`), `Langlands.CategoryTheory.Renard.IndexedSubobjectSums` (for `subobjectSum`) and `Langlands.CategoryTheory.Renard.FiniteTypeFiniteSubcover` (for `finiteTypeFiniteSubcover`). The Mathlib imports are `Algebra.BigOperators.Finprod` and `CategoryTheory.Limits.Preserves.Shapes.Products`.

## Source and route

The governing original is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, A.VIII.2, printed page 267 / PDF page 273. Registered source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The source states "Dans une catégorie de Grothendieck, un objet est un petit projectif si et seulement s'il est projectif de type fini". It gives no proof and cites [37], Pareigis, 4.11, Lemma 1. Pareigis was not read for this unit, and the proof here does not rely on it. The implemented route follows the unchecked outline that Worker 937 gave in the task context; this unit checked and completed that outline. Both directions keep the projectivity conjunct unchanged. Each direction compares coproduct preservation by the integer-module Hom functor `preadditiveCoyonedaInt P : C ⥤ ModuleCat.{v} ℤ` with finite type.

Recall the definitions. `HomSmallProjective.{w} P` is `HomProjective P ∧ HomPreservesCoproducts.{w} P`. The second conjunct says that `preadditiveCoyonedaInt P` preserves colimits of shape `Discrete I` for every `I : Type w`. `IsSourceGrothendieck.{w} C` is `HasCoproducts.{w} C` together with `DirectedSubobjectSumsDistribute.{w} C`, the source AB5 law. `IsFiniteTypeObject P` is `HasSubobjectUnions P` together with the chain condition: no nonempty chain of subobjects different from `⊤` has least upper bound `⊤`.

The direction "projective of finite type implies small projective" uses the AB5 law. The converse uses only `HasCoproducts.{w} C`, the smallness hypothesis, projectivity and coproduct preservation at one index type.

## Finite type implies small

All helper lemmas below are private, except `preservesCoproduct_of_finiteFactor`. That lemma is public so that other modules can reuse it by name (see "Relation to the finite-support assertion").

**Finite subcoproducts.** Fix `f : I → C` with `I : Type w`. For `T : Finset I`, the canonical map `Sigma.desc fun j : T => Sigma.ι f j.1` from the finite subcoproduct to `∐ f` has a retraction (`finIncl_retraction`). The retraction sends the `i`-th summand to the `i`-th inclusion when `i ∈ T`, and to `0` otherwise. So the map is a monomorphism (`mono_finIncl`). `finSub f T` is the subobject it represents, and `finSub_mono` shows that it is monotone in `T`. By `eq_top_of_finSub_le`, every common upper bound `U` of all `finSub f T` is `⊤`. Indeed, each `Sigma.ι f i` factors through `finSub f {i}`, hence through `U`. The factorizations assemble into a section of `U.arrow`. Then `U.arrow` is a split epimorphism and a monomorphism, hence an isomorphism.

**Pullbacks along `g`.** `isLUB_pullback_top` takes a morphism `g : P ⟶ X` and a nonempty family `A j` of subobjects of `X` such that the meets `imageSubobject g ⊓ A j` have least upper bound `imageSubobject g`. It shows that the pullbacks `(Subobject.pullback g).obj (A j)` have least upper bound `⊤`. Let `V` bound all the pullbacks. If `z ≫ g` factors through some `A j`, then `z ≫ cokernel.π V.arrow = 0`, by the pullback square `Subobject.isPullback`. In particular this holds for the kernel of `g`. So `cokernel.π V.arrow` factors through the epimorphism `factorThruImage g` as a morphism `q'` (`Abelian.epiDesc`). For each `j`, pull `factorThruImage g` back along the inclusion of `imageSubobject g ⊓ A j` into `image g`. The pulled-back map is an epimorphism, so cancelling it shows that this meet lies in the kernel of `q'`. Hence `imageSubobject g` lies in that kernel, and `q' = 0`. Therefore `cokernel.π V.arrow = 0`. So `V.arrow` is an epimorphism, hence an isomorphism, and `V = ⊤`.

**Factorization through a finite subcoproduct.** Let `P` be of finite type and `g : P ⟶ ∐ f`. `exists_finite_factor` applies the AB5 law to `T ↦ finSub f T`. This family is indexed by `Finset I : Type w`, is nonempty (`∅`) and is directed, and the meets are taken with `N = imageSubobject g`. The least upper bound `U` it supplies is `⊤` by `eq_top_of_finSub_le`. So the meets `imageSubobject g ⊓ finSub f T` have least upper bound `imageSubobject g`. By `isLUB_pullback_top`, the pullbacks of the `finSub f T` along `g` have least upper bound `⊤` in `Subobject P`. Finite type in its finite-subcover form (`finiteTypeFiniteSubcover C P`) gives finitely many of these pullbacks with least upper bound `⊤`. Write them as pullbacks of `finSub f T` for chosen `T`. Their union `T₀` (a `Finset.sup`) gives a pullback that bounds all of them, so it is `⊤`. Its arrow is then an isomorphism, and `g` factors through the inclusion of the finite subcoproduct over `T₀`.

**Finite decomposition.** With decidable equality on `I`, `finite_decomp` applies to a morphism `x : P ⟶ ∐ f` that factors through some finite subcoproduct `T`. The components `x ≫ Sigma.π f j` vanish for `j ∉ T`, and `x = ∑ j ∈ T, (x ≫ Sigma.π f j) ≫ Sigma.ι f j`. Here `Sigma.π` is Mathlib's projection out of a coproduct in a category with zero morphisms.

**The colimit cocone of integer modules.** `preservesCoproduct_of_finiteFactor` assumes that every morphism `P ⟶ ∐ f` factors through a finite subcoproduct. It proves `PreservesColimit (Discrete.functor f) (preadditiveCoyonedaInt P)`. By `preservesColimit_of_preserves_colimit_cocone` and `isColimitMapCoconeCofanMkEquiv`, it suffices to show that the image cofan, with legs `G.map (Sigma.ι f j)` for `G = preadditiveCoyonedaInt P`, is a colimit. This cocone is built directly with `Cofan.IsColimit.mk`, because `ModuleCat.{v} ℤ` need not have `w`-indexed coproducts when `w` exceeds `v`. For a cofan `t`, the descending map sends `x` to the finitely supported sum `∑ᶠ j, t.inj j (x ≫ Sigma.π f j)`. By the finite decomposition, the support lies in a finite set on which the sum is an ordinary finite sum. This gives additivity. The factorization identities follow from `finsum_eq_single` and `Sigma.ι_π_of_ne`/`Sigma.ι_π_eq_id`. Uniqueness follows by expanding `x` with the finite decomposition and applying the given map term by term.

The objects of `ModuleCat ℤ` reached through `preadditiveCoyonedaInt` carry the `ℤ`-module structure restricted along `ℤ → (End P)ᵐᵒᵖ`. Instance search on the Hom group finds the canonical `ℤ`-module structure instead. The two are equal but not definitionally equal. So the proof takes all linear maps from morphisms of `ModuleCat ℤ` and builds the descending map with `ConcreteCategory.ofHom`. It proves `ℤ`-linearity with the private lemma `map_int_smul`: an additive map between `ℤ`-modules commutes with the integer actions for any `ℤ`-module structures, by `int_smul_eq_zsmul` and `map_zsmul`.

`homPreservesCoproducts_of_finiteType` combines these steps for every `I : Type w` and concludes with `preservesColimitsOfShape_of_discrete`.

## Small projective implies finite type

`finiteType_of_smallProjective` assumes `HasCoproducts.{w} C`, `Small.{w} (Subobject P)`, `HomProjective P` and `HomPreservesCoproducts.{w} P`.

**Unions.** Let `S` be any set of subobjects of `P`. It is `w`-small, so it is enumerated by `Shrink.{w} S` through `equivShrink` (`range_shrink`). The indexed sum `subobjectSum` of this `w`-indexed family exists because `C` has `w`-indexed coproducts and images. Its least upper bound property `isLUB_subobjectSum` gives `HasSubobjectUnions P`.

**The chain condition.** Let `S` be a nonempty chain of subobjects different from `⊤`, and suppose that `S` has least upper bound `⊤`. Enumerate `S` by `F : Shrink.{w} S → Subobject P`. This family is directed because `S` is a chain. Its sum is `⊤`, so its arrow is an isomorphism. Hence the coproduct map `subobjectSumDesc F = Sigma.desc fun j => (F j).arrow`, which equals `subobjectSumπ F ≫ (subobjectSum F).arrow`, is an epimorphism. `homProjectiveComparison` turns `HomProjective P` into Mathlib's `Projective P`. Lifting `𝟙 P` gives `s : P ⟶ ∐ fun j => (F j : C)` with `s ≫ subobjectSumDesc F = 𝟙 P`.

Coproduct preservation at the index type `Shrink.{w} S` makes the image cofan of the coproduct of the `F j` a colimit in `ModuleCat ℤ` (`isColimitOfHasCoproductOfPreservesColimit`). Let `N` be the supremum of the ranges of the legs `G.map (Sigma.ι _ j)`. The quotient map to `M ⧸ N` vanishes on every leg. By uniqueness of maps out of the colimit, it is zero, so `s ∈ N`. The quotient module structure is supplied explicitly as `Submodule.Quotient.module N`, for the instance reason explained above. Before the induction below, a local `let` also fixes the restricted module structure on the carrier.

By `Submodule.iSup_induction`, every `x ∈ N` satisfies `x ≫ subobjectSumDesc F = t ≫ (F j).arrow` for some index `j` and some `t : P ⟶ F j`. For a generator `y ≫ Sigma.ι _ i`, take `j = i` and `t = y`. For `0`, take `t = 0`. For a sum, use directedness to find `k` above both indices, and combine the two morphisms through `Subobject.ofLE` into `F k`. Applied to `s`, this gives `𝟙 P = t ≫ (F j).arrow`. So `(F j).arrow` is a split epimorphism and a monomorphism, hence an isomorphism, and `F j = ⊤`. This contradicts the properness of the members of `S`.

## Main theorem

`smallProjectiveFiniteType C` introduces `hG`, installs `hG.1` as the `HasCoproducts.{w} C` instance and fixes `P`. It proves the forward implication with `finiteType_of_smallProjective` and the converse with `homPreservesCoproducts_of_finiteType hG.2`. The projectivity conjunct passes through unchanged in both directions.

## Relation to the finite-support assertion

The Library statement `Langlands.Renard.SmallProjectiveFiniteSupportStatement` (DAG node `proof.renard-small-projective-finite-support`) is a separate source assertion with its own owner. This unit neither proves nor claims it. The public lemma `preservesCoproduct_of_finiteFactor` proves only that finite-subcoproduct factorization implies coproduct preservation. Its full signature is

```lean
theorem Langlands.Renard.preservesCoproduct_of_finiteFactor {C : Type u} [Category.{v} C]
    [Abelian C] [HasCoproducts.{w} C] {P : C} {I : Type w} (f : I → C)
    (hfact : ∀ g : P ⟶ ∐ f, ∃ (T : Finset I) (g' : P ⟶ ∐ fun j : T => f j),
      g' ≫ Sigma.desc (fun j : T => Sigma.ι f j.1) = g) :
    PreservesColimit (Discrete.functor f) (preadditiveCoyonedaInt P)
```

The separate proof module `Langlands.CategoryTheory.Renard.SmallProjectiveFiniteSupport` reuses it by name for the converse direction of that assertion. `exists_finite_factor` derives such factorizations from finite type and the AB5 law. The forward direction never proves finite factorization for arbitrary morphisms into arbitrary coproducts. It only shows that the one section `s` lies in the span of the summand inclusions.

## Provenance and checks

Worker 840 wrote the Lean proof and this Markdown. Development check `4076a43e-3dd9-4043-9fb8-f68fdc634278` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the module with no errors or warnings. It inspected `Langlands.Renard.smallProjectiveFiniteType` as a theorem with level parameters `w, v, u`. Its only axioms are `propext`, `Classical.choice` and `Quot.sound`. Development checks do not establish exact-target validation, independent acceptance or publication.

Worker 937 later made `preservesCoproduct_of_finiteFactor` public. The change removed its `private` modifier and added a sentence to its docstring and to the module docstring. No statement or proof changed. Development checks `75be94f5-bfeb-441c-b587-ac229b08fd4f` and `1a0cc451-e0ae-486d-8ada-5a1b7a1e89d4`, in the same environment over Library commit `f60a6c408d4d2ab4d0217f8be1dd8745e54a207c`, recompiled the module with no errors or warnings. The second check confirmed by `rfl` that the type of `smallProjectiveFiniteType` is still exactly the statement. It also confirmed that `smallProjectiveFiniteType` and `preservesCoproduct_of_finiteFactor` use only the same three axioms.

This unit proves the A.VIII.2 comparison sentence only. The finite-support characterization, presentations, the regular-module converse and Morita equivalence remain separate obligations.
