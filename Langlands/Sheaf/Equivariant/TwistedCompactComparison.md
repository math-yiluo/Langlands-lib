# Comparison maps for equivariant compactly supported cohomology

Author: Worker 26. Builds on `Langlands.Sheaf.Equivariant.TwistedCompactSupport`
(compactly supported sections of sheaves on a twisted site as representations,
their smooth version `discreteCompactSections` on discrete sheaves, and its
derived functors `discreteCompactDerived`), `Langlands.Sheaf.PointSupport`
(`sheafCompactSections` and `compactDerived` on an arbitrary site with points),
`Langlands.Sheaf.Equivariant.TwistedGodement` (`restrictionAdjunction`:
restriction to the site over `X` is left adjoint to induction),
`Langlands.Representation.Category.SmoothPartAdjunction` and
`Langlands.Representation.Category.ExactInclusion` (the inclusion `SmoothRep.toRep`
is left adjoint to the smooth part and is exact),
`Langlands.Cohomology.DivisibleSystem.PermutationProjective`
(`smoothInvariantsFunctor R G = SmoothRep.toRep ⋙ Rep.invariantsFunctor R G`),
`Langlands.Cohomology.LeftExactHomology` (`derivedNatTrans`) and
`Langlands.Cohomology.ExactBaseChange` (`baseChangeNatTrans`).

## Setting

As in `TwistedCompactSupport`: `C : Type u` with `Category.{v} C`, a morphism
property `P` with `[P.RespectsIso]` and `[P.ContainsIdentities]`, an object `X`,
a group `G : Type uG` with `ρ : G →* Aut X`, a translation-invariant topology `J`
on `P.Over ⊤ X` (so `twistedTopology ρ J` is defined), points
`Φ : I → J.Point.{w}` indexed by `I : Type uI` with `[MulAction G I]`,
`[TopologicalSpace I]` and `[ContinuousConstSMul G I]`, a commutative ring
`R : Type w`, `[LocallySmall.{w} (P.Over ⊤ X)]`, a topology on `G` with
`[IsTopologicalGroup G]`, a local action system
`L : LocalActionSystem (TwistedOver P ρ) G`, and `E : PointEquivariance ρ Φ`.
From the section on invariants on, also `[HasSheafify J (ModuleCat R)]`,
`[HasSheafify (twistedTopology ρ J) (ModuleCat R)]` and
`[L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]`; derived functors
assume `[EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat R))]`, and the
comparison maps also `[EnoughInjectives (Sheaf J (ModuleCat R))]` and the
hypothesis of `TwistedGodement` that every module presheaf on `P.Over ⊤ X` has a
pointwise right Kan extension along `(ι P ρ).op` (true for
`R : Type (max u v uG)` by `hasPointwiseRightKanExtension_moduleCat`).

## Smooth representations

For `R : Type w` and a topological group `G : Type uG`:

- `smoothForget R G`: the module underlying a smooth representation,
  `SmoothRep.toRep ⋙ forget₂ (Rep R G) (ModuleCat R)`. It preserves finite
  limits and finite colimits (`smoothForget_preservesFiniteLimits`,
  `smoothForget_preservesFiniteColimits`), being a composite of exact functors.
- `smoothInvariantsFunctor_preservesFiniteLimits`: the published
  `smoothInvariantsFunctor R G` (the `G`-invariants of a smooth representation)
  preserves finite limits, since Mathlib's `Rep.invariantsFunctor` is a right
  adjoint (`Rep.invariantsAdjunction`).
- `smoothPartInvariantsIso R G`: the invariants of the smooth part of a
  representation are its invariants. A `G`-invariant vector is fixed by the open
  subgroup `⊤`, hence smooth; the components are the evident linear
  equivalences.

## The inclusion of smooth compactly supported sections

`smoothCompactInclusion J R L E` is a natural transformation from
`discreteCompactSections J R L E ⋙ smoothForget R G` to
`(L.discreteSheafInclusion ⋙ restriction ρ J) ⋙ sheafCompactSections J Φ R X₀`,
where `X₀ = (base P ρ).obj` is `X` over itself. Its component at a discrete
sheaf `F` is the image under `forget₂` of the counit of
`SmoothRep.toRepSmoothPartAdjunction` at the representation
`(sheafCompactSectionsRep J R E).obj F`: the inclusion of the smooth vectors.
By `sheafCompactSectionsRepForgetIso` of `TwistedCompactSupport`, the module
underlying that representation is, by definition, the module of compactly
supported sections over `X₀` of the restriction of `F` to the site over `X`.
`smoothCompactInclusion_app_apply` records that the component sends `s` to
`s.1`.

## Invariant compactly supported sections and the edge map

- `discreteInvariantCompactSections J R L E`:
  `discreteCompactSections J R L E ⋙ smoothInvariantsFunctor R G`, from discrete
  sheaves to `ModuleCat R`. It is additive and preserves finite limits.
- `discreteInvariantCompactSectionsIso`: it is isomorphic to the inclusion of
  discrete sheaves, followed by `sheafCompactSectionsRep J R E` and
  `Rep.invariantsFunctor R G`, that is, to the `G`-invariant compactly supported
  global sections (whisker `smoothPartInvariantsIso`).
- `discreteInvariantCompactDerived J R L E q`: its `q`-th right derived functor,
  computed with injective resolutions in the category of discrete sheaves;
  `discreteInvariantCompactDerivedZeroIso` identifies degree zero with the
  functor itself (`Functor.rightDerivedZeroIsoSelf`).
- `invariantEdgeMap J R L E q`: the natural transformation
  `discreteInvariantCompactDerived J R L E q ⟶ discreteCompactDerived J R L E q ⋙
  smoothInvariantsFunctor R G`, defined as `LeftExactHomology.derivedNatTrans`
  for the composite `discreteCompactSections ⋙ smoothInvariantsFunctor`. At an
  object with chosen injective resolution `I`, it is the canonical map from the
  cohomology of the invariants of the complex `discreteCompactSections(I)` to
  the invariants of its cohomology. `isIso_invariantEdgeMap_zero`: it is an
  isomorphism in degree zero (`LeftExactHomology.isIso_derivedNatTrans_zero`).

## The comparison maps

- `restriction_additive`: restriction of module sheaves from the twisted site to
  the site over `X` is additive; it acts on morphisms by whiskering, so
  `map_add` holds by `rfl`.
- `restriction_preservesFiniteColimits`: restriction is the left adjoint in
  `restrictionAdjunction`, so it preserves colimits. With the published
  `restriction_preservesFiniteLimits` of `TwistedCompactSupport` and the
  exactness of the inclusion of discrete sheaves (from
  `LocalActionDiscretePart`), the composite `L.discreteSheafInclusion ⋙
  restriction ρ J` preserves finite limits and finite colimits
  (`discreteRestriction_preservesFiniteLimits`,
  `discreteRestriction_preservesFiniteColimits`).
- `compactComparison J R L E q`: the natural transformation
  `discreteCompactDerived J R L E q ⋙ smoothForget R G ⟶
  (L.discreteSheafInclusion ⋙ restriction ρ J) ⋙ compactDerived J Φ R X₀ q`,
  defined as `ExactBaseChange.baseChangeNatTrans (smoothCompactInclusion J R L E) q`.
  In the notation of that construction, `F₁ = discreteCompactSections`,
  `F₂ = sheafCompactSections J Φ R X₀`, the exact functor `α` is restriction of
  discrete sheaves, the exact functor `β` is `smoothForget`, and `τ` is
  `smoothCompactInclusion`. So the map is the inverse of
  `derivedNatTrans β F₁ q` (an isomorphism because `β` is exact), followed by
  the map `NatTrans.rightDerived τ q` and the comparison
  `compComparisonNatTrans α F₂ q` for the exact functor `α`.

The module proves no property of `compactComparison`. In particular it does not
prove that in degree zero it is `smoothCompactInclusion` under the
degree-zero identifications, nor that it is an isomorphism.

## Provenance and scope

Derived infrastructure. Sources, read in the original by Worker 26:

- Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
  1995–1996 manuscript), §1.5, printed p.11 = PDF p.11: for an étale abelian
  sheaf `F` on `X(G)`, "the functor `F ↦ Γ_{c,X(G)}(F) := {f ∈ F(X(G)) |
  Supp(f) is compact}`" whose higher derived functors are `H^q_c(X(G), F)`, and
  `Γ_{c,X{G}}(F) := lim_→ Γ_{c,X(N)}(F)` over open subgroups `N` of `G`, whose
  higher derived functors are `H^q_c(X{G}, F)`. Corollary 1.5.2(i), printed
  pp.11–12: "For any étale abelian sheaf `F` on `X(G)` there are canonical
  isomorphisms `H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F)`, `g ≥ 0` [sic, for `q ≥ 0`]. In
  particular, the canonical action of `G` on the groups `H^q_c(X, b^*F)` is
  discrete and there is a spectral sequence `E_2^{p,q} = H^p(G, H^q_c(X, b^*F))
  ⟹ H^{p+q}_c(X(G), F)`." The proof (p.12) treats `q = 0` by the fact that
  every element of `H^0_c(X, b^*F)` is fixed by an open subgroup of `G`.
- Harris, *Galois properties of cohomological automorphic forms on GL(n)*
  (1999), §2, printed p.304 = PDF p.6: étale sheaves in smooth
  `Z/ℓ^m Z[S(ẽ)]`-modules over `U(ẽ)` and their compactly supported cohomology
  `H^q_c(U(ẽ)_{F̄}, F(T))`, computed with Berkovich's acyclic embedding.

Correspondence. As recorded in `TwistedCompactSupport`, sections over `X(N)`
are the `N`-invariant sections of the underlying sheaf (proof of Theorem 1.4.2,
printed p.9), so `discreteCompactSections` has the shape of `Γ_{c,X{G}}` and
`discreteCompactDerived` of `H^q_c(X{G}, F)`; taking `N = G`,
`discreteInvariantCompactSections` (the `G`-invariant compactly supported
global sections, by `discreteInvariantCompactSectionsIso`) has the shape of
`Γ_{c,X(G)}` and `discreteInvariantCompactDerived` of `H^q_c(X(G), F)`.
Restriction to the site over `X` plays the role of `b^*`, so
`compactDerived J Φ R X₀ q` applied to the restriction has the shape of
`H^q_c(X, b^*F)`. In degree zero the map of Corollary 1.5.2(i) is the inclusion
of the smooth compactly supported sections into all compactly supported
sections, which is `smoothCompactInclusion`; `compactComparison` is the map it
induces in degree `q` through the exact functors `α` and `β`. Since
`Γ_{c,X(G)}(F)` is the module of `G`-invariants of `Γ_{c,X{G}}(F)`, the printed
spectral sequence is of composite-functor type (this reading is ours; Berkovich
gives no proof of the spectral sequence beyond the reference to
Proposition 1.5.1), and `invariantEdgeMap` has the shape of its edge map
`H^q_c(X(G), F) → E_2^{0,q} = H^q_c(X{G}, F)^G`.

Differences and omissions: an arbitrary site with a group action and an
arbitrary family of points with `PointEquivariance` replace the analytic étale
site and its geometric points; compact support means "contained in a compact
subset of the index space"; derived functors are taken among discrete sheaves
for a chosen local action system rather than on `X(G)_ét`. Not constructed or
proved here: that `compactComparison` is an isomorphism, its degree-zero
identification with `smoothCompactInclusion`, the spectral sequence, the
identification of `invariantEdgeMap` with its edge map, and any analytic
instance. The Library's coverage note records that the printed spectral
sequence fails for `G = ℤ` acting on `ℤ` by translation, so it needs a
compactness hypothesis on `G`; the maps defined here involve no such
hypothesis.

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
