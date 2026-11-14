# The comparison maps through the cohomology of the restriction as a representation

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.TwistedExactGlobalComparison`: for an exact functor
  `incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat R)`, the smooth global sections
  `exactGlobalSections J R incl : 𝒜 ⥤ SmoothRep R G` and their right derived functors
  `exactGlobalDerived J R incl q`, the inclusion
  `exactGlobalInclusion J R incl : exactGlobalSections J R incl ⋙ smoothForget R G ⟶
  exactRestriction J R incl ⋙ sheafSectionsModule J R (base P ρ).obj` (whose component at `F`
  is `forget₂` applied to the counit of the smooth-part adjunction at the global sections
  representation of `incl F`), and the comparison
  `exactGlobalComparison J R incl q := baseChangeNatTrans (exactGlobalInclusion J R incl) q`,
  modelling `H^q(X{G}, F) → H^q(X, b^*F)`.
- `Langlands.Sheaf.Equivariant.TwistedExactCompactComparison`: the compactly supported
  analogues `exactCompactSections`, `exactCompactDerived`, `exactCompactInclusion` and
  `exactCompactComparison J R incl E q`, modelling `H^q_c(X{G}, F) → H^q_c(X, b^*F)`, and
  `exactRestriction J R incl = incl ⋙ restriction ρ J (ModuleCat R)`.
- `Langlands.Sheaf.Equivariant.TwistedRepCohomology`: the representation-valued derived
  functors `sheafGlobalRepDerived J R q` and `sheafCompactRepDerived J R E q`, and the
  comparisons `restrictionGlobalComparison J R q` and `restrictionCompactComparison J R E q`
  from their underlying modules to `H^q(X, b^*F)` and `H^q_c(X, b^*F)`. These are the
  `baseChangeNatTrans` of `(sheafGlobalSectionsRepForgetIso J R).hom` and
  `(sheafCompactSectionsRepForgetIso J E).hom`. With exact coproducts indexed by `G` they
  are isomorphisms, and they define the actions of `G` on `H^q(X, b^*F)` and
  `H^q_c(X, b^*F)`.
- `Langlands.Sheaf.Equivariant.TwistedGlobalSections` and
  `Langlands.Sheaf.Equivariant.TwistedCompactSupport` (through the imports):
  `sheafGlobalSectionsRep J R`, `sheafCompactSectionsRep J R E` and their `ForgetIso`s.
- `Langlands.Representation.Category.SmoothPartAdjunction` (Worker 13, through the
  imports): `SmoothRep.toRepSmoothPartAdjunction R G`, the adjunction between the inclusion
  `SmoothRep.toRep` of smooth representations and the smooth part.
- `Langlands.Cohomology.ExactBaseChange.Paste` (this candidate): `pasteNatTrans` and
  `baseChangeNatTrans_paste_app`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.TwistedOver`.

## Purpose

The comparison maps `H^q(X{G}, F) → H^q(X, b^*F)` and `H^q_c(X{G}, F) → H^q_c(X, b^*F)` of
`TwistedExactGlobalComparison` and `TwistedExactCompactComparison` are maps of modules. Their
sources are smooth representations of `G`. Their targets carry the actions of
`TwistedRepCohomology`. This module factors each comparison map through a morphism of
representations. Consequently the comparison maps commute with the actions of `G`.

## Setting

`C : Type u` is a category, `P` a morphism property with `[P.RespectsIso]` and
`[P.ContainsIdentities]`, `X : C`, `G : Type uG` a topological group, `ρ : G →* Aut X`, `J` a
translation-invariant topology on `P.Over ⊤ X`, and `R : Type w` a commutative ring. `𝒜` is
a category and `incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat R)` a functor.

## Global sections

- `exactGlobalRepInclusion J R incl : exactGlobalSections J R incl ⋙ SmoothRep.toRep ⟶
  incl ⋙ sheafGlobalSectionsRep J R`: the counit of `SmoothRep.toRepSmoothPartAdjunction`
  at the global sections representation of `incl F`. It is a morphism of representations.
- `exactGlobalInclusion_eq_paste`: `exactGlobalInclusion J R incl` is the pasting
  `pasteNatTrans (exactGlobalRepInclusion J R incl) (sheafGlobalSectionsRepForgetIso J R).hom`.
  Componentwise this holds by definition, since the components of
  `sheafGlobalSectionsRepForgetIso` are identities (`Category.comp_id`).

Now let `𝒜` be abelian with enough injectives, and let `incl` be additive and preserve finite
limits and finite colimits. Assume `[HasSheafify (twistedTopology ρ J) (ModuleCat R)]` and
`[EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat R))]`.

- `exactGlobalRepComparison J R incl q : exactGlobalDerived J R incl q ⋙ SmoothRep.toRep ⟶
  incl ⋙ sheafGlobalRepDerived J R q`: the `baseChangeNatTrans` of
  `exactGlobalRepInclusion` along the exact functors `SmoothRep.toRep` and `incl`. Its
  components are morphisms of representations
  `H^q(X{G}, F) → (sheafGlobalRepDerived J R q)(incl F)`.

Assume also `[HasSheafify J (ModuleCat R)]`, `[EnoughInjectives (Sheaf J (ModuleCat R))]`
and that every module presheaf over `X` has a pointwise right Kan extension along
`(ι P ρ).op`.

- `exactGlobalComparison_app_eq J R incl q F`: the component at `F` of
  `exactGlobalComparison J R incl q` equals
  `forget₂ (Rep R G) (ModuleCat R)` applied to the component at `F` of
  `exactGlobalRepComparison J R incl q`, followed by the component at `incl F` of
  `restrictionGlobalComparison J R q`. Proof: rewrite with `exactGlobalInclusion_eq_paste`,
  then apply `baseChangeNatTrans_paste_app`. Here the first square is
  `exactGlobalRepInclusion` (vertical functors `incl` and `SmoothRep.toRep`) and the second
  is `sheafGlobalSectionsRepForgetIso` (vertical functors restriction and `forget₂`).
  `smoothForget` is an abbreviation for the composite `SmoothRep.toRep ⋙ forget₂`.
- `exactGlobalComparison_app_apply`: the same identity on elements.
- `exactGlobalComparison_app_representation J R incl q F g x`: the comparison map sends
  the action of `g` on `x ∈ H^q(X{G}, F)` (`SmoothRep.representation`, the action of the
  underlying representation) to `restrictionGlobalComparison` applied to the action of `g` on the
  image of `x` in `(sheafGlobalRepDerived J R q)(incl F)`. Proof: `exactGlobalComparison_app_apply`
  and `Rep.hom_comm_apply` for the morphism of representations given by
  `exactGlobalRepComparison`.

## Compactly supported sections

Let `I : Type uI` carry a `G`-action and a topology with `[ContinuousConstSMul G I]`, let
`Φ : I → J.Point` be a family of points and `E : PointEquivariance ρ Φ`, and assume
`[LocallySmall.{w} (P.Over ⊤ X)]`.

- `exactCompactRepInclusion J R incl E`, `exactCompactInclusion_eq_paste`: as above, with
  `sheafCompactSectionsRep J R E` and `sheafCompactSectionsRepForgetIso J E`.
- `exactCompactRepComparison J R incl E q : exactCompactDerived J R incl E q ⋙
  SmoothRep.toRep ⟶ incl ⋙ sheafCompactRepDerived J R E q`, under the same hypotheses as
  in the global case, with `[HasSheafify J (ModuleCat R)]` also required here.
- `exactCompactComparison_app_eq`, `exactCompactComparison_app_apply`,
  `exactCompactComparison_app_representation`: the factorization of
  `exactCompactComparison J R incl E q` through `exactCompactRepComparison` and
  `restrictionCompactComparison J R E q`, and its consequence for the actions of `G`.
  The hypotheses and proofs are as in the global case.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`).

- Corollary 1.5.2(i), printed pp.11–12 = PDF pp.11–12: "For any étale abelian sheaf `F` on
  `X(G)` there are canonical isomorphisms `H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F)`, `g ≥ 0`
  [sic, for `q ≥ 0`]. In particular, the canonical action of `G` on the groups
  `H^q_c(X, b^*F)` is discrete and there is a spectral sequence
  `E_2^{p,q} = H^p(G, H^q_c(X, b^*F)) ⟹ H^{p+q}_c(X(G), F)`."
- Theorem 1.6.1(ii), printed p.13 = PDF p.13: "if `X` is compact, then for any quasi-étale
  (resp. étale) abelian sheaf `F` on `X(G)` one has `H^q(X{G}, F) ⥲ H^q(X, b^*F)` and, in
  particular, there is a spectral sequence
  `E_2^{p,q} = H^p(G, H^q(X, b^*F)) ⟹ H^{p+q}(X(G), F)`."

## Provenance and correspondence

The generic setting and the statements are ours. Berkovich deduces the discreteness of the
canonical action on `H^q_c(X, b^*F)` from the isomorphism with `H^q_c(X{G}, F)`. Implicitly
that isomorphism is `G`-equivariant. He does not state this separately or define the action
explicitly. This module proves that the comparison maps commute with the actions of `G`
defined in `TwistedRepCohomology`. That the comparison maps are isomorphisms is not proved
here. The specializations to étale and quasi-étale `G`-sheaves are in
`Langlands.Sheaf.Equivariant.AnalyticRepComparison` (this candidate).
