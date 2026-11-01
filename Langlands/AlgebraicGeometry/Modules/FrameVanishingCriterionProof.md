# Proof of the frame vanishing criterion

This module proves `Langlands.SchemeModule.FrameVanishingCriterionStatement` as the
theorem `Langlands.SchemeModule.frameVanishingCriterion`.

## Statement proved

Let `M` be a module sheaf on a scheme `X`, `U` an open of `X` and `τ` a section of `M`
over `U` that is a frame: on every open `W ≤ U`, the map `r ↦ r • τ|_W` from functions on
`W` to sections of `M` on `W` is bijective. Let `s` be a global section with
`s|_U = a • τ`. Then for every morphism `g : T ⟶ X` with `g⁻¹(U) = T` (hypothesis
`hg : ⊤ ≤ g ⁻¹ᵁ U`), the pullback section `pullbackSection g M s` is zero exactly when the
pulled-back function `g.appLE U ⊤ hg a` is zero.

## Reused helper

`Langlands.SchemeModule.pullback_scalar_eq_zero_iff`: for `f : Y ⟶ X` and an endomorphism `φ` of the
structure module `𝒪_X`, the pullback `f^* φ` is zero exactly when
`f.appTop (φ.app ⊤ 1) = 0`. The proof composes with the isomorphism
`Langlands.Scheme.Modules.pullbackUnitIso f : f^* 𝒪_X ≅ 𝒪_Y`, transposes along the
pullback–pushforward adjunction and uses
`Langlands.Scheme.Modules.pullbackUnitAdjunction` and `structureModule_hom_eq_zero_iff`
(a morphism out of the structure module is zero exactly when its global value at `1` is
zero). The proof reuses this public lemma from
[ResidueLocalChartProof](ResidueLocalChartProof.md), stated for an arbitrary endomorphism.

## Proof of the main theorem

1. Since `g⁻¹(U) = T`, the range of `g` lies in the range of the open immersion
   `U.ι : U ⟶ X`, so `g` factors as `g = g' ≫ U.ι` with
   `g' := IsOpenImmersion.lift U.ι g _`.
2. Let `N' := M.restrict U.ι` and let `τ'` be the global section of `N'` given by `τ`
   restricted to `U.ι ''ᵁ ⊤`; let `a' : Γ(U, ⊤)` be `a` pulled back along `U.ι`.
3. `key`: on each open `W` of `U`, the morphism `sectionHom N' τ' : 𝒪_U ⟶ N'` sends `b`
   to `b • τ|_{U.ι ''ᵁ W}` (after the identification `U.ι.appIso W`). This uses
   `LineBundleDescent.sectionHom_app` and `LineBundleDescent.map_map_apply`.
4. `hiso`: by the frame hypothesis applied to the opens `U.ι ''ᵁ W ≤ U` and `key`,
   every component of `sectionHom N' τ'` is bijective, so `sectionHom N' τ'` is an
   isomorphism (`Scheme.Modules.Hom.isIso_iff_isIso_app`).
5. Define the endomorphism of the structure module of `U`
   `ψ := (restrictUnitIso U.ι).inv ≫ restrict(sectionHom M s) ≫ (sectionHom N' τ')⁻¹`.
   Using `s|_U = a • τ` (`hres`), the restriction of `sectionHom M s` sends `1` to
   `a|_U • τ|_U = (sectionHom N' τ') a'` (`hm`, with `hone` computing the unit
   isomorphism on `1`). Hence `ψ.app ⊤ 1 = a'` (`hψ`).
6. `hval`: `g.appLE U ⊤ hg a = g'.appTop a'`, by substituting `g = g' ≫ U.ι` and using
   `Scheme.Hom.appLE_comp_appLE`.
7. Chain of equivalences. By `pullbackSection_eq_zero_iff`, `pullbackSection g M s = 0`
   iff `g^*(sectionHom M s) = 0`. Since `g = g' ≫ U.ι`, this is equivalent to
   `g'^*(U.ι^*(sectionHom M s)) = 0` (`pullback_map_comp_eq_zero_iff`), and then, via
   `Scheme.Modules.restrictFunctorIsoPullback`, to `g'^*(restrict(sectionHom M s)) = 0`.
   Composing with the isomorphisms `(restrictUnitIso U.ι).inv` and
   `(sectionHom N' τ')⁻¹` does not change vanishing, so this is equivalent to
   `g'^* ψ = 0`. By the helper this is `g'.appTop (ψ.app ⊤ 1) = 0`, that is
   `g'.appTop a' = 0`, which by `hval` is `g.appLE U ⊤ hg a = 0`.

## Provenance

The statement and proof are internal to this project: they package the standard fact
that vanishing of a section of a locally free sheaf of rank one is detected by its local
coefficient in a trivializing frame. The proof is new Lean code built from the existing
Library API (`SectionRatio`, `SectionVanishingTransportProof`, `StructureUnitScalars`,
`LineBundleDescent`) and Mathlib's restriction functor along open immersions.
