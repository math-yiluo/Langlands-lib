# Renard VI.4.1, Theorem: the Hom functor of the single-summand progenerator is an equivalence

Worker 6. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026. The locators are the opening paragraphs of VI.4.1 on printed p.149 / PDF p.155, and the definitions (VI.4.1.3), (VI.4.1.4) and the Theorem with its proof on printed pp.150–151 / PDF pp.156–157. The categorical background is A.VIII.2, printed pp.266–267 / PDF pp.272–273. Registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. All of these pages were read.

## Source content

Renard fixes an irreducible supercuspidal representation (π,V) of G, an irreducible summand (ρ,W) of the restriction of π to ⁰G, and puts (Π,V_Π) = ind_{⁰G}^G(ρ,W). He writes R = End_G(Π). For every smooth (τ,E), Hom_G(Π,τ) is a right R-module, and (VI.4.1.3) defines the functor

F_Π : M(G)[π] → M(R)_d, (τ,E) ↦ Hom_G(Π,τ),

where M(R)_d is the category of unital right R-modules. (VI.4.1.4) defines G_Π(M) = M ⊗_R V_Π. The Theorem says that F_Π is an equivalence of categories between M(G)[π] and M(R)_d, with quasi-inverse G_Π. The proof uses the Proposition of VI.4.1 (Π is a small progenerator), right exactness, compatibility with direct sums and presentations by direct sums of copies of V_Π and of R.

## Lean content

Write H = G(F), with its canonical rational-point topology, and H⁰ = `Plancherel.rationalCommonNormKernel G` for Renard's ⁰G, with the subspace topology.

`RationalSummandHomEquivalenceStatement` has exactly the premises of `RationalSummandSmallProgeneratorStatement` (the Proposition of VI.4.1):

- an arbitrary connected reductive G over an arbitrary nonarchimedean local field F, a maximal split torus inclusion i and a generic cocharacter ν;
- explicit `StandardCocharacterStatement`, relative-root-system and standard-unipotent-closedness premises, from which the finite simple-root index set and the actual semidirect decompositions are derived;
- local compactness, the nonarchimedean group property and Hausdorffness of H;
- π irreducible, and cuspidal in the sense of the published `Aubert.General.IsCuspidal` (every proper standard normalized Jacquet module vanishes);
- ρ an irreducible actual smooth representation of H⁰ with carrier in `Type uV`, with an injective H⁰-equivariant map j : ρ → `SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π`.

Let Π be the published `Induction.compactInductionFunctor (rationalCommonNormKernel G)` applied to `SmoothRep.toRep.obj ρ`. This is the same object as `rationalNormKernelSummandInduction G ρ` in the Proposition module. It is written out here so that the module does not import that file. The conclusion has two parts.

1. Π lies in the published full category `RationalInertiaBlock G (rationalInertiaBaseLift G π)`. This is Renard's M(G)[π]: its objects are the actual smooth representations of H whose irreducible actual subquotients are all isomorphic to actual unramified twists of the lift of π.
2. For the resulting object P of the block, Mathlib's `preadditiveCoyonedaObj P`, from the block to `ModuleCat (End P)ᵐᵒᵖ`, is an equivalence of categories (`Functor.IsEquivalence`).

## Correspondence and conventions

**Right modules.** In Mathlib, multiplication in `End P` is composition: f * g = g ≫ f, that is f ∘ g. The functor `preadditiveCoyonedaObj P` sends Y to the group P ⟶ Y. On this group, r : (End P)ᵐᵒᵖ acts by r • f = r.unop ≫ f, that is f ∘ r.unop, and a morphism Y ⟶ Z acts by postcomposition. So a module over (End P)ᵐᵒᵖ is exactly a unital right module over R = End P, and the functor is Renard's F_Π: Hom_G(Π,τ) with R acting by precomposition. Morphisms of the block are the G-equivariant linear maps, because the block is a full subcategory of actual smooth representations.

**Quasi-inverse.** Renard names the quasi-inverse G_Π(M) = M ⊗_R V_Π. The Lean statement asserts only that F_Π is an equivalence. Every equivalence has a quasi-inverse, unique up to natural isomorphism, but the identification of that quasi-inverse with M ⊗_R V_Π is not stated.

**Universes.** π and ρ have carriers in `Type uV`, and Π has carrier in `Type (max uF uV)`. So the block is formed at carrier universe `max uF uV`, from the lift of π along the published fully faithful `SmoothRep.universeLiftFunctor` (`rationalInertiaBaseLift`), as in the Proposition and in Worker 1758's `RationalUniversalSmallProgeneratorStatement`. The Hom groups of the block live in `Type (max uF uV)`, so the target is the category of right R-modules with carrier in `Type (max uF uV)`. Renard has no universe restriction. Coefficients are ℂ in universe zero.

**Abelianness.** The published `Langlands.Renard.SmallProgeneratorEquivalenceStatement` (A.VIII.2) assumes an abelian category with coproducts. The present statement is made directly on the actual preadditive full block. It neither assumes nor asserts that the block is abelian or has coproducts. So it is not obtained by specializing that A.VIII.2 statement without further proof.

**Choice of ρ.** As in the Proposition, Renard's ρ is an irreducible summand of Res π, and the Lean statement takes every irreducible ρ with an injective equivariant map into Res π. By VI.3.2 these are, up to isomorphism, the summands. The Lean statement does not use or assert this comparison.

There is no splitness, characteristic-zero, admissibility, compactness or finite-dimensionality premise on ρ or π.

## Scope

This module defines a Prop-valued target only. It does not prove block membership or the equivalence. The Proposition of VI.4.1 (Π is a small progenerator of the block) is the separate statement `RationalSummandSmallProgeneratorStatement`. The later results of VI.4 (the convolution algebra H(G,ρ), the structure of R and the center of the block) are not stated here.
