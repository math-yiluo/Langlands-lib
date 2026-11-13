# Equivariant global sections and their cohomology on a twisted site

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.LocalActionCohomology`: `sheafSectionsRep R J a`, the
  sections over an object `U` of module sheaves as a representation of a monoid `K`
  acting on `U` by endomorphisms through `a : K →* (End U)ᵐᵒᵖ`, with its additivity and
  left exactness.
- `Langlands.Sheaf.Equivariant.TwistedOver`: the twisted category `TwistedOver P ρ`, its
  topology `twistedTopology ρ J`, the base object `base P ρ` (the identity of `X`), the
  action `baseAction P ρ : G →* (End (base P ρ))ᵐᵒᵖ` (`g` acts through the endomorphism
  `baseEndo g⁻¹`), and the restriction functor `restriction ρ J` to the site over `X`.
- `Langlands.Sheaf.Equivariant.TwistedCompactComparison` and, through it,
  `TwistedCompactSupport`, `TwistedGodement`,
  `Langlands.Representation.Category.SmoothPartAdjunction` and
  `Langlands.Cohomology.ExactBaseChange`. They provide the smooth part functor
  `SmoothRep.smoothPartFunctor` with its adjunction `SmoothRep.toRepSmoothPartAdjunction`
  (left exactness comes from the instance `smoothPartFunctor_isRightAdjoint`),
  `smoothForget`, the exactness instances for restriction, and `baseChangeNatTrans`. This
  module is the global-sections counterpart of their compactly supported constructions.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.TwistedOver`.

## Purpose

Berkovich's `Γ_{X{G}}` and `H^q(X{G}, F)` are the ordinary (not compactly supported)
counterparts of `Γ_{c,X{G}}` and `H^q_c(X{G}, F)`. The latter are defined for an arbitrary
twisted site in `TwistedCompactSupport`, with supports taken in a family of points. This
module gives the former for an arbitrary twisted site. It needs no points: the global
sections are the sections over the base object.

## Sections over an object

Let `C : Type u` be a category, `J` a Grothendieck topology on `C`, and `R : Type w` a
commutative ring.

- `sheafSectionsModule J R U`: the sections over `U` of module sheaves,
  `sheafToPresheaf ⋙ evaluation at U`. By `sheafSectionsModule_obj` (`rfl`) its value at
  `F` is `F.obj.obj (op U)`. It is additive and left exact, as a composite of the
  limit-preserving functors `sheafToPresheaf` and evaluation.
- With `[HasSheafify J (ModuleCat R)]` and `[EnoughInjectives (Sheaf J (ModuleCat R))]`:
  - `sectionsDerived J R U q`: the cohomology over `U`, the right derived functors of
    `sheafSectionsModule J R U`;
  - `sectionsDerivedZeroIso J R U`: in degree zero it is `sheafSectionsModule J R U`;
  - `sectionsDerivedIso J R U I q`: it is the homology of the sections over `U` of any
    injective resolution `I`;
  - `isZero_sectionsDerived_succ_of_injective`: it vanishes in positive degrees on injective
    sheaves.

## Global sections on a twisted site

Let `P` be a morphism property of `C` with `[P.RespectsIso]` and `[P.ContainsIdentities]`,
let `X : C`, let `G : Type uG` be a group with `ρ : G →* Aut X`, and let `J` be a
translation-invariant topology on `P.Over ⊤ X`.

- `sheafGlobalSectionsRep J R`: global sections of module sheaves on the twisted site as
  representations of `G`. It is `sheafSectionsRep` at the base object with the action
  `baseAction P ρ`. It is additive and left exact.
- `sheafGlobalSectionsRepForgetIso J R`: the underlying module of this representation is
  `sheafSectionsModule J R (base P ρ).obj` applied to the restriction to the site over `X`.
  The components are identities.

From here on `G` is a topological group.

- `sheafGlobalSectionsSmooth J R`: the smooth part of `sheafGlobalSectionsRep J R`, a functor
  to `SmoothRep R G`. It is additive and left exact.

## Discrete sheaves

Let `L : LocalActionSystem (TwistedOver P ρ) G` be a local action system.

- `discreteGlobalSections J R L`: the smooth global sections of discrete module sheaves,
  that is, `sheafGlobalSectionsSmooth` after the inclusion of discrete sheaves. This is the
  shape of Berkovich's `Γ_{X{G}}`. It is additive, and it is left exact under
  `[HasSheafify (twistedTopology ρ J) (ModuleCat R)]` and
  `[L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]`, which make discrete sheaves an
  abelian category whose inclusion is left exact (`LocalActionDiscretePart`).
- With also `[EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat R))]`:
  - `discreteGlobalDerived J R L q`: its right derived functors, computed with injective
    resolutions among discrete sheaves, as smooth representations of `G`. This is the shape
    of Berkovich's `H^q(X{G}, F)`;
  - `discreteGlobalDerivedZeroIso`, `discreteGlobalDerivedIso`,
    `isZero_discreteGlobalDerived_succ_of_injective`: degree zero, computation by injective
    resolutions, and vanishing on injectives, as above.

## Comparison with the site over `X`

- `smoothGlobalInclusion J R L`: the natural inclusion of the smooth global sections of a
  discrete sheaf into the sections over the base object of its restriction to the site over
  `X`. Its component at `F` is the image under `forget₂ (Rep R G) (ModuleCat R)` of the
  counit of the smooth-part adjunction at the global sections representation. By
  `smoothGlobalInclusion_app_apply` (`rfl`) it sends a smooth section to itself.
- `globalComparison J R L q`, under the hypotheses of `TwistedCompactComparison`
  (sheafification and enough injectives on both sites, finite equivariant refinements, and
  pointwise right Kan extensions along `(ι P ρ).op`): the published
  `ExactBaseChange.baseChangeNatTrans` of `smoothGlobalInclusion` along the exact functors
  `smoothForget R G` and restriction. Its source is `discreteGlobalDerived J R L q`
  followed by `smoothForget`. Its target is the restriction followed by
  `sectionsDerived J R (base P ρ).obj q`. This is the shape of Berkovich's map
  `H^q(X{G}, F) → H^q(X, b^*F)`. Nothing is claimed about it being an isomorphism.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (folder
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).

- §1.2, printed pp.4–5 = PDF pp.4–5: "We denote by `Γ_{X(G)}` the global sections functor
  on `X(G)~_qét` (resp. `X(G)~_ét`), i.e., `Γ_{X(G)}(F) = F(X(G))`. [...] We also denote
  by `Γ_{X{G}}` the functor from `X(G)~_qét` (resp. `X(G)~_ét`) to the category of
  (discrete) `G`-sets by `Γ_{X{G}}(F) = lim_→ F(X_{G/N}(G))`, where `N` runs through open
  subgroups of `G`. [...] It follows also that for any open subgroup `N ⊂ G` one has
  `Γ_{X{G}}(F)^N = F(X_{G/N}(G))`. The high direct images of the functor `Γ_{X{G}}` on the
  category of abelian sheaves will be denoted by `H^q(X{G}, F)`."
- Theorem 1.6.1, printed p.13 = PDF p.13: "(ii) if `X` is compact, then for any
  quasi-étale (resp. étale) abelian sheaf `F` on `X(G)` one has
  `H^q(X{G}, F) ⥲ H^q(X, b^*F)`".

## Provenance and correspondence

The generic setting is ours (derived infrastructure), parallel to `TwistedCompactSupport`
and `TwistedCompactComparison`:

- Berkovich's `Γ_{X{G}}(F) = lim_N F(X_{G/N}(G))` with `Γ_{X{G}}(F)^N = F(X_{G/N}(G))` is
  modelled by the union over open subgroups `N` of the `N`-invariant global sections, which
  is the smooth part of the global sections representation. In the twisted model the
  sections over `X_{G/N}(G)` are not a separate object; they are represented by the
  `N`-invariant global sections.
- The derived functors are taken among discrete sheaves of `R`-modules, not among all
  abelian sheaves. Their comparison with derived functors of abelian sheaves is not
  formalized.
- The comparison map is the base change of the evident inclusion. That it agrees with
  Berkovich's isomorphism of Theorem 1.6.1(ii) is not formalized. That theorem itself is
  not proved.

## Not formalized here

Theorem 1.6.1, its spectral sequence, the cohomology `H^q(X(G), F)` of invariant global
sections, and any statement that `globalComparison` is an isomorphism.
