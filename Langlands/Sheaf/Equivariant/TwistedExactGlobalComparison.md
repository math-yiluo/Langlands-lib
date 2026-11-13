# Global comparison maps for exact abelian subcategories of twisted sheaves

Author: Worker 26. Generalizes the discrete-sheaf part of Worker 26's published module
`Langlands.Sheaf.Equivariant.TwistedGlobalSections`, the way the published
`Langlands.Sheaf.Equivariant.TwistedExactCompactComparison` generalizes its compactly
supported counterpart. It uses:

- `Langlands.Sheaf.Equivariant.TwistedGlobalSections` (Worker 26): `sheafSectionsModule`
  and `sectionsDerived` (sections over an object and their derived functors),
  `sheafGlobalSectionsRep` and `sheafGlobalSectionsSmooth` (global sections of module
  sheaves on a twisted site, as a representation and its smooth part);
- `Langlands.Sheaf.Equivariant.TwistedExactCompactComparison` (Worker 26):
  `exactRestriction J R incl`, its additivity and its exactness instances, and, through
  its imports, `smoothForget` with its exactness, the base object `base P ρ`, the
  restriction `restriction ρ J`, and `smoothInvariantsFunctor` (the `G`-invariant vectors
  of a smooth representation) from `Langlands.Cohomology.DivisibleSystem.PermutationProjective`;
- `SmoothRep.toRepSmoothPartAdjunction` from
  `Langlands.Representation.Category.SmoothPartAdjunction`, the adjunction between
  smooth representations and representations whose counit is the inclusion of the
  smooth part;
- `Langlands.Cohomology.ExactBaseChange` (`baseChangeNatTrans`) and
  `Langlands.Cohomology.LeftExactHomology` (`derivedNatTrans`,
  `isIso_derivedNatTrans_zero`).

All declarations are in the namespace `Langlands.Sheaf.Equivariant.TwistedOver`.

## Purpose

`TwistedGlobalSections` constructs, for the discrete sheaves of a local action system on
a twisted site, Berkovich's smooth global sections `Γ_{X{G}}`, their derived functors
`H^q(X{G}, F)` and the comparison maps `H^q(X{G}, F) → H^q(X, b^*F)`. The constructions
use only that discrete sheaves form an abelian category with enough injectives whose
inclusion into module sheaves on the twisted site is additive and exact. This module
repeats them for any category `𝒜` with a functor
`incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat R)`, with these facts as hypotheses.
It also defines what `TwistedGlobalSections` does not: the invariant global sections
`Γ_{X(G)}`, their derived functors `H^q(X(G), F)`, and the edge maps
`H^q(X(G), F) → H^q(X{G}, F)^G`. Equality with the published constructions for discrete
sheaves is not stated.

The intended instance is the inclusion of the locally discrete sheaves of
`LocalActionSmoothPart`, which form an abelian category with enough injectives and have
an exact inclusion under `HasAdmissibleRefinements`. On the twisted étale site these are
Berkovich's étale `G`-sheaves; `AnalyticEtaleCohomology`, submitted together with this
module, applies it to them. No family of points is used: the global sections are the
sections over the base object.

## Data and universes

- A category `C : Type u` with `Category.{v} C`, a morphism property `P` with
  `[P.RespectsIso]` and `[P.ContainsIdentities]`, and an object `X`. Write
  `X₀ = (base P ρ).obj`, `X` over itself by its identity.
- A group `G : Type uG` with `ρ : G →* Aut X`, and `[TopologicalSpace G]`,
  `[IsTopologicalGroup G]`.
- A topology `J` on `P.Over ⊤ X` with `[IsTranslationInvariant J]`.
- A commutative ring `R : Type w`; sheaves take values in `ModuleCat.{w} R`, and smooth
  representations are `SmoothRep.{w, uG, w} R G`.
- A category `𝒜 : Type uA` with `Category.{vA} 𝒜`, and a functor
  `incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat R)`.

From the section on exactness on: `[Abelian 𝒜]`, `[incl.Additive]` and
`[PreservesFiniteLimits incl]`. Derived functors also need `[EnoughInjectives 𝒜]`. The
comparison maps also need `[HasSheafify J (ModuleCat R)]`, `[PreservesFiniteColimits incl]`,
`[EnoughInjectives (Sheaf J (ModuleCat R))]`, and the hypothesis of `TwistedGodement`
that every module presheaf on `P.Over ⊤ X` has a pointwise right Kan extension along
`(ι P ρ).op`. Sheafification on the twisted site is not assumed.

## The inclusion for all module sheaves

- `sheafSmoothGlobalInclusion J R`: the natural transformation from
  `sheafGlobalSectionsSmooth J R ⋙ smoothForget R G` to
  `restriction ρ J ⋙ sheafSectionsModule J R X₀`, on all module sheaves on the twisted
  site. Its component at `F` is the counit of `SmoothRep.toRepSmoothPartAdjunction` at
  the representation `sheafGlobalSectionsRep J R F`, followed by the forgetful functor to
  modules. The module underlying `sheafGlobalSectionsRep J R F` is definitionally the
  module of sections over `X₀` of the restriction of `F`, so this lands in the stated
  target. Naturality is the naturality of the counit.
- `sheafSmoothGlobalInclusion_app_apply` (by `rfl`): a smooth global section is sent to
  itself.

## Functors on `𝒜`

No abelian structure is needed here; additivity uses `[Preadditive 𝒜]` and
`[incl.Additive]`.

- `exactGlobalSections J R incl`: `incl ⋙ sheafGlobalSectionsSmooth J R`, Berkovich's
  `Γ_{X{G}}` on `𝒜`, valued in `SmoothRep R G`. Additive (instance).
- `exactGlobalInclusion J R incl`: `sheafSmoothGlobalInclusion J R` whiskered by `incl`,
  the inclusion `Γ_{X{G}}(incl F) → Γ(X₀, b^*F)`, from
  `exactGlobalSections ⋙ smoothForget R G` to
  `exactRestriction J R incl ⋙ sheafSectionsModule J R X₀`. `exactGlobalInclusion_app`
  (by `rfl`) computes its component, and `exactGlobalInclusion_app_apply` (by `rfl`)
  says that a smooth global section is sent to itself.
- `exactInvariantGlobalSections J R incl`: `exactGlobalSections` followed by
  `smoothInvariantsFunctor R G`, the role of Berkovich's `Γ_{X(G)}`, valued in
  `ModuleCat R`. Additive (instance).

## Exactness

Instances `exactGlobalSections_preservesFiniteLimits` and
`exactInvariantGlobalSections_preservesFiniteLimits`: both functors are left exact, as
composites of `incl` with left exact functors.

## Derived functors

With `[EnoughInjectives 𝒜]`:

- `exactGlobalDerived J R incl q`: the right derived functors of `exactGlobalSections`,
  computed with injective resolutions in `𝒜`, valued in `SmoothRep R G`; the shape of
  Berkovich's `H^q(X{G}, F)`.
  - `exactGlobalDerivedZeroIso`: in degree zero it is `exactGlobalSections`
    (Mathlib's `rightDerivedZeroIsoSelf`).
  - `exactGlobalDerivedIso I q`: for an injective resolution `I` of `F` in `𝒜`, its value
    at `F` is the degree `q` cohomology of `exactGlobalSections` applied to `I`.
  - `isZero_exactGlobalDerived_succ_of_injective`: it vanishes in positive degrees on
    injective objects of `𝒜`. This theorem does not use `[PreservesFiniteLimits incl]`.
- `exactInvariantGlobalDerived J R incl q`: the right derived functors of
  `exactInvariantGlobalSections`, valued in `ModuleCat R`; the shape of Berkovich's
  `H^q(X(G), F)`. `exactInvariantGlobalDerivedZeroIso` identifies degree zero with
  `exactInvariantGlobalSections`.
- `exactInvariantGlobalEdgeMap J R incl q`: the natural transformation from
  `exactInvariantGlobalDerived q` to `exactGlobalDerived q ⋙ smoothInvariantsFunctor R G`,
  the edge map `H^q(X(G), F) → H^q(X{G}, F)^G`. It is
  `LeftExactHomology.derivedNatTrans` for the left exact functor `smoothInvariantsFunctor`
  and `exactGlobalSections`. The instance `isIso_exactInvariantGlobalEdgeMap_zero` says it
  is an isomorphism in degree zero (`isIso_derivedNatTrans_zero`).

## The comparison maps

- `exactGlobalComparison J R incl q`: the natural transformation from
  `exactGlobalDerived q ⋙ smoothForget R G` to
  `exactRestriction J R incl ⋙ sectionsDerived J R X₀ q`, the shape of Berkovich's map
  `H^q(X{G}, F) → H^q(X, b^*F)`. It is `ExactBaseChange.baseChangeNatTrans` of
  `exactGlobalInclusion` along the exact functors `smoothForget R G` and
  `exactRestriction J R incl`. Nothing is claimed about it being an isomorphism.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (folder
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).

- §1.2, printed pp.4–5 = PDF pp.4–5: "We denote by `Γ_{X(G)}` the global sections functor
  on `X(G)~_qét` (resp. `X(G)~_ét`), i.e., `Γ_{X(G)}(F) = F(X(G))`. The high direct images
  of `Γ_{X(G)}` on the category of abelian sheaves will be denoted by `H^q(X(G), F)`. We
  also denote by `Γ_{X{G}}` the functor from `X(G)~_qét` (resp. `X(G)~_ét`) to the
  category of (discrete) `G`-sets by `Γ_{X{G}}(F) = lim_→ F(X_{G/N}(G))`, where `N` runs
  through open subgroups of `G`. [...] For a `G`-set `Σ`, let `X_Σ` denote the disjoint
  union `⊔_{σ∈Σ} X_σ` (`X_σ` are copies of `X`) [...]. It follows also that for any open
  subgroup `N ⊂ G` one has `Γ_{X{G}}(F)^N = F(X_{G/N}(G))`. The high direct images of the
  functor `Γ_{X{G}}` on the category of abelian sheaves will be denoted by
  `H^q(X{G}, F)`. For any abelian sheaf `F` there is a spectral sequence
  `E_2^{p,q} = H^p(G, H^q(X{G}, F)) ⟹ H^{p+q}(X(G), F)`."
- Theorem 1.6.1, printed p.13 = PDF p.13: "(ii) if `X` is compact, then for any
  quasi-étale (resp. étale) abelian sheaf `F` on `X(G)` one has
  `H^q(X{G}, F) ⥲ H^q(X, b^*F)`".

## Provenance and correspondence

Derived infrastructure. The correspondence with Berkovich is the one recorded in
`TwistedGlobalSections`: `exactGlobalSections` models `Γ_{X{G}}` by the smooth part of
the global sections representation (the union over open subgroups `N` of the
`N`-invariant global sections), `exactRestriction` plays the role of `b^*`, and
`exactGlobalComparison q` has the shape of Berkovich's map in degree `q`. The following
choices are ours:

- The generalization from discrete sheaves to an exact abelian subcategory `𝒜`, made to
  apply the constructions to the locally discrete sheaves of `LocalActionSmoothPart`.
- `Γ_{X(G)}` is modelled by the `G`-invariant vectors of `Γ_{X{G}}`. Berkovich's quote
  above gives `Γ_{X{G}}(F)^N = F(X_{G/N}(G))`; for `N = G` the `G`-set `G/G` is a point,
  `X_{G/G}` is one copy of `X`, and this reads `Γ_{X{G}}(F)^G = F(X(G)) = Γ_{X(G)}(F)`.
- The edge map is the comparison between the derived functors of the composite
  `Γ_{X(G)} = (-)^G ∘ Γ_{X{G}}` and the composite of `(-)^G` with the derived functors of
  `Γ_{X{G}}`. It has the shape of the edge map `H^q(X(G), F) → E_2^{0,q}` of Berkovich's
  spectral sequence quoted above, read as a composite-functor spectral sequence. That
  reading is ours, and the identification is not formalized.
- The derived functors are taken in `𝒜`, not among all abelian sheaves.

## Not formalized here

That the comparison maps are isomorphisms (Theorem 1.6.1(ii)); the identification of the
degree-zero comparison with `exactGlobalInclusion`; any spectral sequence; and the
equality of these constructions with those of `TwistedGlobalSections` for discrete
sheaves.
