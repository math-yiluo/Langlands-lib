# Equivariant compactly supported sections on a twisted site

Author: Worker 26. Combines `Langlands.Sheaf.Equivariant.TwistedOver` (the
twisted category over `X`, translations, relabelling, the base object and its
`G`-action), `Langlands.Sheaf.PointSupport` (supports via germs at points and
compactly supported sections), `Langlands.Sheaf.Equivariant.LocalActionCohomology`
(`actionRepresentation`, `actionIntertwiningMap`),
`Langlands.Sheaf.Equivariant.LocalActionDiscretePart` (discrete sheaves) and
`Langlands.Representation.Category.SmoothPartAdjunction` (the smooth-part
functor, right adjoint to the inclusion of smooth representations).

## Setting

`C : Type u` with `Category.{v} C`, a morphism property `P` with
`[P.RespectsIso]`, an object `X`, a group `G : Type uG`, `ρ : G →* Aut X`, a
Grothendieck topology `J` on `P.Over ⊤ X`, a family of points
`Φ : I → J.Point.{w}` with `I : Type uI` and an action `[MulAction G I]`.

`PointEquivariance ρ Φ` is a structure with one field:
`fiberIso g i : translate P ρ g ⋙ (Φ (g • i)).fiber ≅ (Φ i).fiber`. It
identifies the fiber of `Φ (g • i)` over a translate `gU` with the fiber of `Φ i`
over `U`, naturally in `U`. For a point over a geometric point `x̄` of a space
`X` with a left action, the points of `gU` (structure map `U.hom ≫ ρ g`) over
`g x̄` are the points of `U` over `x̄`. The structure is data to be supplied by a
specialization; no instance is constructed here.

## Germs

- `eq_comp_rho_inv_of_comp_rho_eq`, `comp_rho_inv_comp_rho`: cancelling `ρ g`
  against `ρ g⁻¹` on arrows into `X`.
- `translateInvIso g V : g(g⁻¹V) ≅ V` (identity arrow), and `untranslate g f :
  g⁻¹V ⟶ U` for `f : V ⟶ gU` (same arrow). `translate_map_untranslate`:
  translating `untranslate g f` back gives `translateInvIso g V` followed by `f`.
- `relabelNatTrans F g`: for a presheaf `F` on the twisted category, the natural
  transformation from `(translate g)ᵒᵖ ⋙ ιᵒᵖ ⋙ F` to `ιᵒᵖ ⋙ F` with components
  `F.map (relabel ρ g U).op`. Naturality is `ι_map_comp_relabel`; its components
  are isomorphisms because relabelling is.
- With `R : Type w` a commutative ring and `[LocallySmall.{w} (P.Over ⊤ X)]`:
  - `toPresheafFiber_eq_zero_iff E Q g i x t`: for a module presheaf `Q` on
    `P.Over ⊤ X`, the germ of `t ∈ Q(gU)` at the point `Φ (g • i)` and the element
    of its fiber corresponding to `x` vanishes exactly when the germ of `t`, as a
    section of `(translate g)ᵒᵖ ⋙ Q` over `U`, vanishes at `Φ i` and `x`. Both
    sides are unfolded with Mathlib's criterion `toPresheafFiber_eq_iff'` (a germ
    vanishes when the section vanishes after restriction to some element of the
    fiber category). A witness `f : V ⟶ gU` on the left becomes
    `untranslate g f` on the right, and a witness `k` on the right becomes
    `translate g k` on the left; `fiberIso` and its naturality match the fiber
    elements.
  - `toPresheafFiber_relabel_eq_zero_iff`: applying `relabelNatTrans` does not
    change whether a germ vanishes, since it induces an isomorphism on fibers.

## Supports of translated global sections

With `[P.ContainsIdentities]`:

- `isTerminalBaseObj P ρ`: the base object `X` (identity structure map) is
  terminal in `P.Over ⊤ X`.
- `actionRepresentation_baseAction_eq`: `g` acts on a global section `s` by
  restricting along the morphism over `X` underlying `baseEndo g⁻¹`, then
  applying the relabelling by `g⁻¹` (from `relabel_comp_ι_map_untwist`).
- `support_actionRepresentation E F g s` (with `[LocallySmall.{w} _]`): the
  support of `g · s`, for the points `Φ` and the restriction `ιᵒᵖ ⋙ F`, is
  `g • support s`. The index `i` lies in the support of `g · s` exactly when
  `g⁻¹ • i` lies in the support of `s`: combine the two germ lemmas with the
  restriction formula of germs, and use that fibers over the terminal base
  object are singletons.

## Compactly supported sections as representations

Assume moreover `[TopologicalSpace I]` and `[ContinuousConstSMul G I]`.

- `isCompactlySupported_actionRepresentation`: if the support of `s` lies in a
  compact `K`, that of `g · s` lies in the compact set `g • K`.
- `compactRepresentation R E F`: the representation of `G` on
  `compactSubmodule Φ R (ιᵒᵖ ⋙ F) X` obtained by restricting
  `actionRepresentation F (baseAction P ρ)` (`compactRepresentation_apply`).
- `compactIntertwiningMap E φ`: a morphism of presheaves restricts to an
  intertwiner (naturality of `φ`).
- `compactSectionsRep R E : ((TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat R) ⥤ Rep R G`,
  additive.

## Sheaves and derived functors

Assume `[IsTranslationInvariant J]`, so that `twistedTopology ρ J` is defined.

- `sheafCompactSectionsRep J R E`: the composite with `sheafToPresheaf`;
  additive. `sheafCompactSectionsRepForgetIso`: its underlying modules are
  `restriction ρ J ⋙ sheafCompactSections J Φ R X`.
- `restriction_preservesFiniteLimits`: restriction of module sheaves from the
  twisted site preserves finite limits; its composite with `sheafToPresheaf`
  is `sheafToPresheaf ⋙ (whiskeringLeft).obj ιᵒᵖ`, and `sheafToPresheaf`
  reflects finite limits.
- `sheafCompactSectionsRep_preservesFiniteLimits` (with
  `[HasSheafify J (ModuleCat R)]`): left exact, by the forget isomorphism, the
  left exactness of `sheafCompactSections` and reflection of finite limits by
  the forgetful functor from `Rep`.
- With a topology on `G` and `[IsTopologicalGroup G]`:
  `sheafCompactSectionsSmooth J R E` is `sheafCompactSectionsRep J R E`
  followed by the smooth-part functor, which is a right adjoint
  (instance `smoothPartFunctor_isRightAdjoint`, from
  `SmoothRep.toRepSmoothPartAdjunction`) and so left exact; it is additive and
  left exact.
- For `L : LocalActionSystem (TwistedOver P ρ) G`: `discreteCompactSections
  J R L E` is the restriction to discrete sheaves; additive, and left exact
  under `[HasSheafify J _]`, `[HasSheafify (twistedTopology ρ J) _]` and
  `[L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]`. With
  `[EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat R))]`,
  `discreteCompactDerived J R L E q` is its `q`-th right derived functor, with
  `discreteCompactDerivedZeroIso`, `discreteCompactDerivedIso` (computation by
  an injective resolution among discrete sheaves) and
  `isZero_discreteCompactDerived_succ_of_injective`.

## Provenance and scope

Derived infrastructure. Sources, read in the original by Worker 26:

- Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
  1995–1996 manuscript), §1.5, printed p.11 = PDF p.11: the support
  `Supp(f) = {x ∈ X | f_x ≠ 0}` of `f ∈ F(X(G))`, the functors
  `Γ_{c,X(G)}(F) = {f ∈ F(X(G)) | Supp(f) is compact}` and
  `Γ_{c,X{G}}(F) := lim_→ Γ_{c,X(N)}(F)` over open subgroups `N`, and
  `H^q_c(X{G}, F)` as the values of the higher direct images of the latter.
  §1.4, printed p.7: `G`-sheaves and the translates `ᵍU = U ×_{X,g⁻¹} X`.
- Harris, *Galois properties of cohomological automorphic forms on GL(n)*
  (1999), §2, printed p.304 = PDF p.6: étale sheaves in smooth
  `Z/ℓ^m Z[S(ẽ)]`-modules ("what Berkovich calls discrete") and the functor
  `RΓ_c`, with compactly supported cohomology `H^q_c(U(ẽ)_{F̄}, F(T))`.

Correspondence. `sheafCompactSectionsSmooth` sends a sheaf to the smooth
vectors of its compactly supported global sections. In Berkovich's setting,
sections over `X(N)` are identified with the `N`-invariant sections of the
underlying `G`-sheaf (proof of Theorem 1.4.2, step A.4, printed p.9), so
`Γ_{c,X{G}}(F)` is the union over open subgroups `N` of the `N`-invariant
compactly supported sections, that is, the smooth vectors.
`discreteCompactDerived` is the corresponding right derived functor on discrete
sheaves, the shape of `H^q_c(X{G}, F)` with its smooth `G`-action as used by
Harris. Differences: an arbitrary site with a group action and an arbitrary
family of points with `PointEquivariance` replace the analytic étale site and
its geometric points; compact support means "contained in a compact subset of
the index space"; the derived functors are taken in the category of discrete
sheaves for a chosen local action system. No comparison with Berkovich's
derived functors on `X(G)_ét`, no Godement computation and no analytic
instance (sites, points, `PointEquivariance`, Key Lemma actions) is
constructed or assumed here. The noncompact-group caveat for the composite
spectral sequence (recorded by Worker 16) does not concern these definitions.

Universes: `C : Type u` with `Category.{v} C`, `G : Type uG`, `I : Type uI`,
fibers, ring and modules in universe `w`, smooth representations in
`SmoothRep.{w, uG, w} R G`.

Source registrations: Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`.
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, file
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

The instances introduced here have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and instance
scopes are unchanged.
