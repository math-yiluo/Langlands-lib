# The action of `G` on the cohomology of the restriction of a twisted sheaf

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.TwistedLeftInduction` (this candidate): with exact
  coproducts of modules indexed by `G`, restriction from the twisted site sends injective
  sheaves to injective sheaves (`restriction_preservesInjectiveObjects`).
- `Langlands.Sheaf.Equivariant.TwistedGlobalSections`: `sheafGlobalSectionsRep J R`, the
  global sections of module sheaves on the twisted site as representations of `G` (`g` acts
  by restriction along the endomorphism `g⁻¹` of the base object `base P ρ`), with
  `sheafGlobalSectionsRepForgetIso J R`, identifying its underlying module with the sections
  over `base P ρ` of the restriction (identity components); `sectionsDerived J R U q`, the
  right derived functors of the sections over `U` of module sheaves.
- `Langlands.Sheaf.Equivariant.TwistedCompactSupport` (through the imports):
  `PointEquivariance ρ Φ`, `sheafCompactSectionsRep J R E` (compactly supported global
  sections as representations of `G`) and `sheafCompactSectionsRepForgetIso J E`;
  `Langlands.Sheaf.PointSupport`: `sheafCompactSections J Φ R U` and its right derived
  functors `compactDerived J Φ R U q`.
- `Langlands.Sheaf.Equivariant.TwistedCompactComparison` (through the imports): restriction
  is additive and, given pointwise right Kan extensions along `(ι P ρ).op`, preserves finite
  colimits; `TwistedCompactSupport` shows it preserves finite limits.
- `Langlands.Cohomology.ExactBaseChange` and `Langlands.Cohomology.ExactBaseChange.ResolutionProof`:
  the base change transformation `baseChangeNatTrans τ n : Rⁿ F₁ ⋙ β ⟶ α ⋙ Rⁿ F₂` of a
  transformation `τ : F₁ ⋙ β ⟶ α ⋙ F₂` along exact functors `α`, `β`,
  `quasiIso_mapResolutionAugmentation`, and the criterion
  `isIso_baseChangeNatTrans_app_of_acyclic`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.TwistedOver`.

## Purpose

Let `F` be a module sheaf on the twisted site of a `G`-object `X`, and `b^*F` its restriction
to the site over `X`. The global sections and the compactly supported global sections of
`F` are representations of `G`, with underlying modules the corresponding sections of
`b^*F`. Their right derived functors are representations of `G`. When coproducts of modules
indexed by `G` exist and are exact, their underlying modules are identified with
`H^q(X, b^*F)` and `H^q_c(X, b^*F)`. This puts an action of `G` on `H^q(X, b^*F)` and on
`H^q_c(X, b^*F)`. Berkovich uses these actions in Corollary 1.5.2(i) and Theorem 1.6.1(ii)
(see below).

## Setting

`C : Type u` is a category, `P` a morphism property with `[P.RespectsIso]` and
`[P.ContainsIdentities]`, `X : C`, `G : Type uG` a group, `ρ : G →* Aut X`, `J` a
translation-invariant topology on `P.Over ⊤ X`, and `R : Type w` a commutative ring.

## Global sections

Assume `[HasSheafify (twistedTopology ρ J) (ModuleCat R)]` and
`[EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat R))]`.

- `sheafGlobalRepDerived J R q : Sheaf (twistedTopology ρ J) (ModuleCat R) ⥤ Rep R G`: the
  right derived functors of `sheafGlobalSectionsRep J R`.
- `sheafGlobalRepDerivedZeroIso`: in degree zero it is `sheafGlobalSectionsRep J R`.
- `sheafGlobalRepDerivedIso J R I q`: it is the homology of the global sections
  representation of any injective resolution `I`.
- `isZero_sheafGlobalRepDerived_succ_of_injective`: it vanishes in positive degrees on
  injective sheaves.

Assume also `[HasSheafify J (ModuleCat R)]`, `[EnoughInjectives (Sheaf J (ModuleCat R))]`
and that every module presheaf over `X` has a pointwise right Kan extension along
`(ι P ρ).op`, so that restriction is exact.

- `restrictionGlobalComparison J R q`: the transformation from
  `sheafGlobalRepDerived J R q ⋙ forget₂ (Rep R G) (ModuleCat R)` to
  `restriction ρ J (ModuleCat R) ⋙ sectionsDerived J R (base P ρ).obj q`. It is
  `baseChangeNatTrans` of `(sheafGlobalSectionsRepForgetIso J R).hom` along the exact
  functors restriction and `forget₂`.

Assume finally `[HasColimitsOfShape (Discrete G) (ModuleCat R)]` and
`[HasExactColimitsOfShape (Discrete G) (ModuleCat R)]` (they hold when `G` is `w`-small, by
`discrete_hasColimitsOfShape` and `discrete_hasExactColimitsOfShape`).

- `isIso_restrictionGlobalComparison_app J R q F`: the component at `F` is an isomorphism.
  The proof applies `isIso_baseChangeNatTrans_app_of_acyclic` to the injective resolution
  `K` of `F` (`injectiveResolution F`) and to its restriction, with augmentation
  `mapResolutionAugmentation` and `ψ = 𝟙`. The comparison of complexes `Φ` is the
  componentwise application of the isomorphism `sheafGlobalSectionsRepForgetIso`, hence a
  quasi-isomorphism. The terms of `K` are injective, and so are their restrictions
  (`restriction_preservesInjectiveObjects`), so both are acyclic.
- `restrictionGlobalCohomologyIso J R q`: the resulting natural isomorphism
  `sheafGlobalRepDerived J R q ⋙ forget₂ (Rep R G) (ModuleCat R) ≅
  restriction ρ J (ModuleCat R) ⋙ sectionsDerived J R (base P ρ).obj q`. Through it, the
  representation `(sheafGlobalRepDerived J R q).obj F` is an action of `G` on
  `H^q(X, b^*F)`.

## Compactly supported global sections

Let `I : Type uI` carry a `G`-action and a topology with `[ContinuousConstSMul G I]`, let
`Φ : I → J.Point` be a family of points and `E : PointEquivariance ρ Φ`. Assume
`[LocallySmall.{w} (P.Over ⊤ X)]`, `[HasSheafify J (ModuleCat R)]`,
`[HasSheafify (twistedTopology ρ J) (ModuleCat R)]` and
`[EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat R))]`.

- `sheafCompactRepDerived J R E q`: the right derived functors of
  `sheafCompactSectionsRep J R E`, as representations of `G`.
- `sheafCompactRepDerivedZeroIso`, `sheafCompactRepDerivedIso`,
  `isZero_sheafCompactRepDerived_succ_of_injective`: degree zero, computation by injective
  resolutions, and vanishing on injectives. The last does not need `HasSheafify J`.

With also `[EnoughInjectives (Sheaf J (ModuleCat R))]` and the pointwise right Kan
extensions:

- `restrictionCompactComparison J R E q`: from
  `sheafCompactRepDerived J R E q ⋙ forget₂ (Rep R G) (ModuleCat R)` to
  `restriction ρ J (ModuleCat R) ⋙ compactDerived J Φ R (base P ρ).obj q`, the
  `baseChangeNatTrans` of `(sheafCompactSectionsRepForgetIso J E).hom`.

With also exact coproducts of modules indexed by `G`:

- `isIso_restrictionCompactComparison_app`: its components are isomorphisms, by the same
  argument as in the global case.
- `restrictionCompactCohomologyIso J R E q`: the natural isomorphism
  `sheafCompactRepDerived J R E q ⋙ forget₂ (Rep R G) (ModuleCat R) ≅
  restriction ρ J (ModuleCat R) ⋙ compactDerived J Φ R (base P ρ).obj q`. Through it,
  `(sheafCompactRepDerived J R E q).obj F` is an action of `G` on `H^q_c(X, b^*F)`.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`).

- Corollary 1.5.2(i), printed pp.11–12 = PDF pp.11–12: "For any étale abelian sheaf `F` on
  `X(G)` there are canonical isomorphisms `H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F)`, `g ≥ 0`
  [sic, for `q ≥ 0`]. In
  particular, the canonical action of `G` on the groups `H^q_c(X, b^*F)` is discrete and
  there is a spectral sequence `E_2^{p,q} = H^p(G, H^q_c(X, b^*F)) ⟹ H^{p+q}_c(X(G), F)`."
- Theorem 1.6.1(ii), printed p.13 = PDF p.13: "if `X` is compact, then for any quasi-étale
  (resp. étale) abelian sheaf `F` on `X(G)` one has `H^q(X{G}, F) ⥲ H^q(X, b^*F)` and, in
  particular, there is a spectral sequence
  `E_2^{p,q} = H^p(G, H^q(X, b^*F)) ⟹ H^{p+q}(X(G), F)`."

## Provenance and correspondence

The generic setting is ours. Berkovich does not define the action on `H^q_c(X, b^*F)` and
`H^q(X, b^*F)` explicitly; he calls it canonical. Here it is the action carried by the right
derived functors of the representation-valued (compactly supported) global sections on the
twisted site, transported to `H^q(X, b^*F)` (resp. `H^q_c(X, b^*F)`) along the isomorphisms
above. In degree zero, `sheafGlobalRepDerivedZeroIso` (resp. `sheafCompactRepDerivedZeroIso`)
identifies the representation with the (compactly supported) global sections
representation. That this identification is compatible with `restrictionGlobalCohomologyIso`
(resp. `restrictionCompactCohomologyIso`) and the degree-zero isomorphism of the target is
not proved.

Not formalized here: that the action is discrete (smooth), which is part of Corollary
1.5.2(i); the isomorphisms `H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F)` and
`H^q(X{G}, F) ⥲ H^q(X, b^*F)`, and their compatibility with the actions; the spectral
sequences.
