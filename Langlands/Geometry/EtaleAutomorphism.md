# Automorphisms of a scheme acting on its small étale site

Author: Worker 13. Built on Mathlib's small étale site `Y.Etale` with
`Y.smallEtaleTopology`, Mathlib's `MorphismProperty.Over.map`, and Mathlib's
equivalence of sheaf categories induced by an equivalence of sites
(`Equivalence.sheafCongr`).

Let `Y : Scheme.{u}` be a scheme and let `σ : Y ≅ Y` be an automorphism.
Coefficients lie in an arbitrary category `A`. From the section on additivity
onwards, `A` is `ModuleCat R` for a commutative ring `R : Type u`.

## The site

- `siteMap σ : Y.Etale ⥤ Y.Etale` sends an étale `Y`-scheme `(U, u)` to
  `(U, u ≫ σ.hom)` and is the identity on underlying morphisms. It is
  Mathlib's `MorphismProperty.Over.map` along the étale morphism `σ.hom`.
- `siteEquivalence σ` is the equivalence with inverse `siteMap σ.symm`. Its
  unit and counit come from Mathlib's `Over.mapId` and `Over.mapComp`.
- `mem_smallEtaleTopology_iff` restates Mathlib's covering condition of the
  small étale topology pointwise. A sieve on `U` covers exactly when every
  point of `U` is the image of a point under some arrow of the sieve. The
  condition that the arrow is étale, present in Mathlib's form, holds
  automatically.
- `siteMap_isCocontinuous σ` proves that `siteMap σ` is cocontinuous. Let `f`
  be an arrow of a covering sieve on the translated object, through which a
  point lifts. The same underlying morphism, now over `σ⁻¹`, is an arrow into
  `U`. Its translate is `f` precomposed with an isomorphism whose underlying
  morphism is the identity, so it lies in the sieve.
- The two cocontinuity instances for the functor and inverse of
  `siteEquivalence σ` give the dense-subsite instance that Mathlib's
  `sheafCongr` requires.

## Sheaves

- `sheafEquivalence A σ` is Mathlib's `sheafCongr` for
  `siteEquivalence σ.symm`. `translate A σ` is its functor. It sends a sheaf
  `F` to the sheaf `(U, u) ↦ F(U, u ≫ σ)`, the precomposition of `F` with
  `siteMap σ`. As an equivalence it is exact.
- `translateComp A σ τ : translate A σ ⋙ translate A τ ≅ translate A (τ ≪≫ σ)`
  and `translateId A : translate A (Iso.refl Y) ≅ 𝟭` are whiskerings of
  Mathlib's `Over.mapComp` and `Over.mapId`.
- `translateCongr A h`, for an equality `h : σ = τ`, is the whiskering of
  Mathlib's `Over.mapCongr`. All three isomorphisms have identity
  underlying morphisms on étale schemes.

## Sections

- `terminalIso σ` identifies the translate of the terminal object of
  `Y.Etale` with the terminal object. It is unique, since an equivalence
  preserves terminal objects (`isTerminalSiteMapObj`).
- `sectionsIso A σ` identifies sections of a translated sheaf over the
  terminal object with sections of the sheaf, naturally, by restriction along
  `terminalIso σ`.
- `sectionsIso_comp`, `sectionsIso_congr` and `sectionsIso_id` prove the
  compatibility of `sectionsIso` with `translateComp`, `translateCongr` and
  `translateId`. In each, both sides restrict along arrows from the terminal
  object into a terminal object, which are equal.

## Module sheaves

For `A = ModuleCat R`, `translate_additive` and `translate_linear` prove that
translation is additive and `R`-linear. Both hold because morphisms are
whiskered componentwise. `translate_preservesInjectiveObjects` is Mathlib's
preservation of injective objects by equivalences.

## Provenance and scope

This is derived infrastructure. Harris, *Galois properties of cohomological
automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39-2 (1999), Theorem 5.7,
printed p.313, uses the action of `Gal(F̄/F)` on étale cohomology of Shimura
varieties `S_K(N)` with coefficients. Worker 13 read this passage in the
original. Such actions arise from automorphisms of a base-changed scheme. This
module supplies the action of a single automorphism on the étale site and on
étale sheaves. Not treated here: group actions, equivariant sheaves,
cohomology, base change to a separable closure, and any comparison of
`translate` with Mathlib's inverse or direct image functors.

Source registration:
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

The module imports only Mathlib.
