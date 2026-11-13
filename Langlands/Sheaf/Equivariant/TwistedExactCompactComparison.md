# Compact comparison maps for exact abelian subcategories of twisted sheaves

Author: Worker 26. Generalizes Worker 26's published modules
`Langlands.Sheaf.Equivariant.TwistedCompactComparison`,
`Langlands.Cohomology.DiscreteSheafDerivedComparison` and
`Langlands.Cohomology.DiscreteSheafDerivedComparisonHomology`. It uses from them, and
from the infrastructure they rest on:

- `Langlands.Sheaf.Equivariant.TwistedCompactSupport` (Worker 26):
  `sheafCompactSectionsRep`, `sheafCompactSectionsSmooth` (Berkovich's `Γ_{c,X{G}}` on
  module sheaves on a twisted site), the restriction `restriction ρ J` and its left
  exactness;
- `Langlands.Sheaf.Equivariant.TwistedCompactComparison` (Worker 26): `smoothForget`
  and its exactness, and the right exactness of `restriction ρ J`, which rests on the
  right Kan extensions of `TwistedGodement`;
- `Langlands.Sheaf.PointSupport`: `sheafCompactSections` and `compactDerived` on a site
  with points;
- `Langlands.Cohomology.DiscreteSheafDerivedComplex`: `sheafCompactComplex` and
  `sheafCompactComplexHomologyIso`;
- `Langlands.Cohomology.DiscreteSheafDerivedComparison`: `derivedComplexMap` and
  `derivedComplexMap_homology`;
- `Langlands.Cohomology.DiscreteSheafDerivedComparisonHomology`:
  `rightDerivedCompIsoOfResolution_refl_hom_comp_derivedNatTrans`;
- `Langlands.Cohomology.AcyclicResolution.DerivedCompositeComparison`:
  `derivedCompComparison`, its naturality and `derivedCompComparison_homology`;
- `Langlands.Cohomology.DerivedPlus`, `Langlands.Cohomology.DerivedExactPostcomposition`
  and `Langlands.Cohomology.DerivedExactComposition`: `derivedComplex`, `homologyIso`,
  `isZero_homology_of_neg`, `derivedPostcompIso`, `derivedCompIso`,
  `derivedCompIso_hom_homology`, `mapDerivedCategoryHomologyIso`;
- `Langlands.Cohomology.ExactBaseChange` (`baseChangeNatTrans`) and
  `Langlands.Cohomology.LeftExactHomology` (`derivedNatTrans`,
  `isIso_derivedNatTrans_zero`);
- `DerivedSections.isZero_rightDerived_succ_of_preservesHomology` from
  `Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction`;
- `smoothInvariantsFunctor` (the `G`-invariant vectors of a smooth representation) from
  `Langlands.Cohomology.DivisibleSystem.PermutationProjective`.

## Purpose

The published modules above build, for the discrete sheaves of a local action system on
a twisted site, Berkovich's comparison maps `H^q_c(X{G}, F) → H^q_c(X, b^*F)`, the edge
maps `H^q_c(X(G), F) → H^q_c(X{G}, F)^G`, and the comparison
`RΓ_c(X{G}, F) → RΓ_c(X, b^*F)` of derived complexes with its cohomology. The
constructions use only three facts about discrete sheaves: they form an abelian category
with enough injectives, and their inclusion into module sheaves on the twisted site is
additive and exact. This module repeats the constructions for any category `𝒜` with a
functor `incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat R)`, assuming these three
facts as hypotheses. The definitions and proofs are those of the published modules, with
the inclusion of discrete sheaves replaced by `incl`. Equality with the published
constructions for discrete sheaves is not stated.

The intended instance is the inclusion of the locally discrete sheaves of
`LocalActionSmoothPart`, which are abelian with enough injectives and have an exact
inclusion under `HasAdmissibleRefinements`. For the twisted étale site these are
Berkovich's étale `G`-sheaves; `AnalyticEtaleComparison` applies this module to them.

All declarations are in `Langlands.Sheaf.Equivariant.TwistedOver`.

## Data and universes

- A category `C : Type u` with `Category.{v} C`, a morphism property `P` with
  `[P.RespectsIso]` and `[P.ContainsIdentities]`, and an object `X`. Write
  `X₀ = (base P ρ).obj`, `X` over itself.
- A topological group `G : Type uG` (`[TopologicalSpace G] [IsTopologicalGroup G]`) and
  `ρ : G →* Aut X`.
- A topology `J` on `P.Over ⊤ X` with `[IsTranslationInvariant J]`, and
  `[LocallySmall.{w} (P.Over ⊤ X)]`.
- A commutative ring `R : Type w`; sheaves take values in `ModuleCat.{w} R`.
- Points `Φ : I → J.Point.{w}` indexed by `I : Type uI` with `[MulAction G I]`,
  `[TopologicalSpace I]` and `[ContinuousConstSMul G I]`, and
  `E : PointEquivariance ρ Φ`.
- A category `𝒜 : Type uA` with `Category.{vA} 𝒜` and a functor
  `incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat R)`.

From the section on exactness on: `[Abelian 𝒜]`, `[incl.Additive]`,
`[HasSheafify J (ModuleCat R)]`, `[PreservesFiniteLimits incl]` and
`[PreservesFiniteColimits incl]`. Sheafification on the twisted site is not assumed. The
right exactness of restriction also needs the hypothesis of `TwistedGodement` that every
module presheaf on `P.Over ⊤ X` has a pointwise right Kan extension along `(ι P ρ).op`.
Derived functors need `[EnoughInjectives 𝒜]`, and the comparison maps also
`[EnoughInjectives (Sheaf J (ModuleCat R))]`. Complexes use derived categories chosen by
`[HasDerivedCategory.{w₁} 𝒜]`, `[HasDerivedCategory.{w₂} (Sheaf J (ModuleCat R))]`,
`[HasDerivedCategory.{w₃} (SmoothRep R G)]` and `[HasDerivedCategory.{w₄} (ModuleCat R)]`.

## The inclusion for all module sheaves

- `sheafSmoothCompactInclusion J R E`: the natural transformation from
  `sheafCompactSectionsSmooth J R E ⋙ smoothForget R G` to
  `restriction ρ J ⋙ sheafCompactSections J Φ R X₀`, on all module sheaves on the twisted
  site. Its component at `F` is the counit of Mathlib's adjunction
  `SmoothRep.toRepSmoothPartAdjunction` (the inclusion of the smooth part of a
  representation), applied to the representation `sheafCompactSectionsRep J R E` of `F`
  and followed by the forgetful functor to modules. Naturality is the naturality of the
  counit.
- `sheafSmoothCompactInclusion_app_apply` (by `rfl`): a smooth compactly supported
  section is sent to itself.

## Functors on `𝒜`

No abelian structure is needed in this section; additivity uses `[Preadditive 𝒜]` and
`[incl.Additive]`.

- `exactCompactSections J R incl E`: `incl ⋙ sheafCompactSectionsSmooth J R E`,
  Berkovich's `Γ_{c,X{G}}` on `𝒜`, valued in `SmoothRep R G`.
- `exactRestriction J R incl`: `incl ⋙ restriction ρ J`, the role of `b^*`.
- `exactCompactInclusion J R incl E`: `sheafSmoothCompactInclusion` whiskered by `incl`,
  the inclusion `Γ_{c,X{G}}(incl F) → Γ_c(X₀, b^*F)`. `exactCompactInclusion_app`
  (by `rfl`) computes its component.
- `exactInvariantCompactSections J R incl E`: `exactCompactSections` followed by
  `smoothInvariantsFunctor R G`, the role of `Γ_{c,X(G)}`.
- Instances `exactCompactSections_additive`, `exactRestriction_additive` and
  `exactInvariantCompactSections_additive`.

## Exactness

Instances: `exactCompactSections` and `exactInvariantCompactSections` preserve finite
limits, as composites of left exact functors; `exactRestriction` preserves finite limits
and, under the Kan extension hypothesis, finite colimits, as the composite of `incl` with
the exact restriction.

## Derived functors and comparison maps

- `exactCompactDerived J R incl E q`: the right derived functors of
  `exactCompactSections`, computed with injective resolutions in `𝒜`;
  `exactCompactDerivedZeroIso` identifies degree zero with `exactCompactSections`.
- `exactInvariantCompactDerived J R incl E q`: the right derived functors of
  `exactInvariantCompactSections`; `exactInvariantCompactDerivedZeroIso` identifies
  degree zero.
- `exactInvariantEdgeMap J R incl E q`: the natural transformation from
  `exactInvariantCompactDerived q` to `exactCompactDerived q ⋙ smoothInvariantsFunctor`.
  It is `LeftExactHomology.derivedNatTrans` for the left exact functor
  `smoothInvariantsFunctor` and `exactCompactSections`. The instance
  `isIso_exactInvariantEdgeMap_zero` says it is an isomorphism in degree zero.
- `exactCompactComparison J R incl E q`: the natural transformation from
  `exactCompactDerived q ⋙ smoothForget R G` to
  `exactRestriction ⋙ compactDerived J Φ R X₀ q`. It is
  `ExactBaseChange.baseChangeNatTrans` of `exactCompactInclusion`: the inverse of the
  isomorphism `derivedNatTrans` for the exact functor `smoothForget`, then the map of
  derived functors induced by `exactCompactInclusion`, then the comparison
  `compComparisonNatTrans` for the exact functor `exactRestriction`.
- `isZero_exactRestriction_rightDerived F q`: the right derived functors of the exact
  functor `exactRestriction` vanish in positive degrees
  (`isZero_rightDerived_succ_of_preservesHomology`).

## Complexes

- `exactCompactComplex J R incl E`: `DerivedPlus.derivedComplex` of
  `exactCompactSections`, the complex `RΓ_c(X{G}, incl F)` in
  `DerivedCategory.Plus (SmoothRep R G)`. `exactCompactComplexHomologyIso` identifies
  its cohomology in degree `q` with `exactCompactDerived q`, and
  `isZero_exactCompactComplex_homology` gives vanishing in negative degrees.
- `exactRestrictionCompactComparison J R Φ incl`: the natural transformation from the
  derived complex of `exactRestriction ⋙ sheafCompactSections J Φ R X₀` to
  `exactRestriction ⋙ sheafCompactComplex J Φ R X₀`, both followed by
  `DerivedCategory.Plus.ι`. Its components are `derivedCompComparison` for the identity
  of `exactRestriction ⋙ sheafCompactSections`, applicable because the positive derived
  functors of `exactRestriction` vanish; naturality is
  `derivedCompComparison_naturality`.
- `exactCompactComplexComparison J R incl E`: the comparison
  `RΓ_c(X{G}, incl F) → RΓ_c(X₀, b^*F)` in `DerivedCategory (ModuleCat R)`, from
  `exactCompactComplex ⋙ DerivedCategory.Plus.ι` followed by the derived functor of
  `smoothForget R G`, to `exactRestriction ⋙ sheafCompactComplex J Φ R X₀` followed by
  `DerivedCategory.Plus.ι`. It is the composite of
  `(derivedPostcompIso (exactCompactSections J R incl E) (smoothForget R G)).hom`,
  `derivedComplexMap (exactCompactInclusion J R incl E)` and
  `exactRestrictionCompactComparison`.
- `exactInclusionRestrictionComparison_homology E F n`: on cohomology in degree `n`,
  under the identifications `DerivedPlus.homologyIso`, the last two factors induce
  `(LeftExactHomology.derivedNatTrans (smoothForget R G) (exactCompactSections J R incl E) n).app F`
  followed by `(exactCompactComparison J R incl E n).app F`. The proof rewrites with
  `derivedCompComparison_homology` and `derivedComplexMap_homology`, then unfolds
  `baseChangeNatTrans` and cancels the inverse of `derivedNatTrans`.
- `exactCompactComplexComparison_homology_eq E F n`: the degree `n` cohomology of
  `exactCompactComplexComparison`, followed by `DerivedPlus.homologyIso` for the target,
  equals `mapDerivedCategoryHomologyIso (smoothForget R G) n`, then `smoothForget`
  applied to `DerivedPlus.homologyIso` for the source, then
  `exactCompactComparison J R incl E n`. The proof: `derivedCompIso` for the identity
  isomorphism is `derivedPostcompIso`; `derivedCompIso_hom_homology` computes the
  cohomology of the first factor up to the classical comparison
  `rightDerivedCompIsoOfResolution`; the previous theorem treats the other two factors;
  and `rightDerivedCompIsoOfResolution_refl_hom_comp_derivedNatTrans` cancels the
  classical comparison against `derivedNatTrans`.
- `exactCompactComplexForgetHomologyIso E F n`: the degree `n` cohomology of the image of
  `RΓ_c(X{G}, incl F)` under the derived `smoothForget` is the module underlying
  `exactCompactDerived n`: `mapDerivedCategoryHomologyIso` followed by `smoothForget`
  applied to `exactCompactComplexHomologyIso`.
- `exactCompactComplexComparison_homology E F n`: the same identity as the previous
  theorem with the target identified by `sheafCompactComplexHomologyIso` and the source
  by `exactCompactComplexForgetHomologyIso`; it is a regrouping.

So, after these identifications, `exactCompactComplexComparison` induces in every degree
`n ≥ 0` the map `exactCompactComparison J R incl E n`. It is not proved that these maps
are isomorphisms.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (folder
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).

- §1.5, printed p.11 = PDF p.11: "The values of the high direct images of the functor
  F ↦ Γ_{c,X{G}}(F) := lim_→ Γ_{c,X(N)}(F), where N runs through open subgroups of G,
  are denoted by H^q_c(X{G}, F)."
- Corollary 1.5.2(i), printed pp.11–12 = PDF pp.11–12: "For any étale abelian sheaf F on
  X(G) there are canonical isomorphisms H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F), g ≥ 0" [sic,
  for q ≥ 0].

## Provenance and correspondence

Derived infrastructure. The correspondence with Berkovich is the one recorded in
`TwistedCompactComparison` and `DiscreteSheafDerivedComparison`:
`exactCompactComparison q` has the shape of Berkovich's map in degree `q`,
`exactCompactComplex` the shape of `RΓ_c(X{G}, F)`, and `exactRestriction` the role of
`b^*`. Berkovich states the comparison only on cohomology groups; the map of complexes
is our construction. The generalization from discrete sheaves to an exact abelian
subcategory is ours. Its purpose is to apply the constructions to the locally discrete
sheaves of `LocalActionSmoothPart`, which model Berkovich's étale `G`-sheaves.

## Not formalized here

That the comparison maps are isomorphisms; the spectral sequence of Corollary 1.5.2(i);
the identification of the degree-zero comparison with `exactCompactInclusion`; and the
equality of these constructions with the published ones for discrete sheaves.
