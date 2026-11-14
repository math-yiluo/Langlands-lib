# Derived global section complexes for exact abelian subcategories of twisted sheaves

Author: Worker 26. This is the global (not compactly supported) counterpart of the
section "Complexes" of Worker 26's published module
`Langlands.Sheaf.Equivariant.TwistedExactCompactComparison`. The proofs repeat the
proofs given there. It uses:

- `Langlands.Sheaf.Equivariant.TwistedExactGlobalComparison` (Worker 26):
  `exactGlobalSections`, `exactInvariantGlobalSections`, `exactGlobalInclusion`, their
  derived functors `exactGlobalDerived` and `exactInvariantGlobalDerived`, and the
  comparison `exactGlobalComparison`, which is `ExactBaseChange.baseChangeNatTrans` of
  `exactGlobalInclusion`;
- `Langlands.Sheaf.Equivariant.TwistedGlobalSections` (Worker 26): `sheafSectionsModule`
  (sections over an object of a site) and `sectionsDerived` (its right derived
  functors);
- `Langlands.Sheaf.Equivariant.TwistedExactCompactComparison` (Worker 26):
  `exactRestriction` (the restriction of `incl F` to the site over `X`) and
  `isZero_exactRestriction_rightDerived` (its positive derived functors vanish);
- `Langlands.Cohomology.DiscreteSheafDerivedComparison`: `derivedComplexMap` and
  `derivedComplexMap_homology`;
- `Langlands.Cohomology.DiscreteSheafDerivedComparisonHomology`:
  `rightDerivedCompIsoOfResolution_refl_hom_comp_derivedNatTrans`;
- `Langlands.Cohomology.AcyclicResolution.DerivedCompositeComparison`:
  `derivedCompComparison`, `derivedCompComparison_naturality` and
  `derivedCompComparison_homology`;
- `Langlands.Cohomology.DerivedPlus`, `Langlands.Cohomology.DerivedExactPostcomposition`
  and `Langlands.Cohomology.DerivedExactComposition`: `derivedComplex`, `homologyIso`,
  `isZero_homology_of_neg`, `derivedPostcompIso`, `derivedCompIso`,
  `derivedCompIso_hom_homology` and `mapDerivedCategoryHomologyIso`;
- `Langlands.Cohomology.ExactBaseChange` (`baseChangeNatTrans`,
  `compComparisonNatTrans`) and `Langlands.Cohomology.LeftExactHomology`
  (`derivedNatTrans`).

All declarations are in the namespace `Langlands.Sheaf.Equivariant.TwistedOver`.

## Purpose

`TwistedExactGlobalComparison` defines Berkovich's `H^q(X{G}, -)` and `H^q(X(G), -)` and
the comparison `H^q(X{G}, F) → H^q(X, b^*F)` one degree at a time. The spectral sequences
of Berkovich's §1.2 and Theorem 1.6.1(ii), and composite-functor statements of the shape
used in the Library's `Langlands.Cohomology.EquivariantComposite.Statement`, are about the
derived complexes `RΓ(X{G}, F)` and `RΓ(X(G), F)`. For compact supports these complexes
and the comparison of complexes are in `TwistedExactCompactComparison`. This module adds
them for global sections.

## Data and universes

- A category `C : Type u` with `Category.{v} C`, a morphism property `P` with
  `[P.RespectsIso]` and `[P.ContainsIdentities]`, and an object `X`. Write
  `X₀ = (base P ρ).obj`, `X` over itself.
- A topological group `G : Type uG` (`[TopologicalSpace G] [IsTopologicalGroup G]`) and
  `ρ : G →* Aut X`.
- A topology `J` on `P.Over ⊤ X` with `[IsTranslationInvariant J]`.
- A commutative ring `R : Type w`; sheaves take values in `ModuleCat.{w} R`.
- An abelian category `𝒜 : Type uA` with `Category.{vA} 𝒜` and enough injectives, and an
  additive, left exact functor `incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat R)`.
- Derived categories are chosen by `[HasDerivedCategory.{w₁} 𝒜]`,
  `[HasDerivedCategory.{w₂} (Sheaf J (ModuleCat R))]`,
  `[HasDerivedCategory.{w₃} (SmoothRep R G)]` and
  `[HasDerivedCategory.{w₄} (ModuleCat R)]`, each only where it is used.

The comparison section adds `[HasSheafify J (ModuleCat R)]`,
`[PreservesFiniteColimits incl]`, `[EnoughInjectives (Sheaf J (ModuleCat R))]` and the
hypothesis of `TwistedGodement` that every module presheaf on `P.Over ⊤ X` has a pointwise
right Kan extension along `(ι P ρ).op`. These are the hypotheses of
`exactGlobalComparison`; with them `exactRestriction` is exact.

## Sections over an object of a site

For a site `(C, J)` with sheafification and enough injectives for module sheaves, and an
object `U`:

- `sheafSectionsComplex J R U`: `DerivedPlus.derivedComplex` of `sheafSectionsModule J R U`,
  the complex `RΓ(U, F)` in `DerivedCategory.Plus (ModuleCat R)`.
- `sheafSectionsComplexHomologyIso J R U F q`: its cohomology in degree `q` is
  `(sectionsDerived J R U q).obj F`.
- `isZero_sheafSectionsComplex_homology`: it has no cohomology in negative degrees.

## Complexes on `𝒜`

- `exactGlobalComplex J R incl`: `DerivedPlus.derivedComplex` of `exactGlobalSections`,
  the complex `RΓ(X{G}, incl F)` in `DerivedCategory.Plus (SmoothRep R G)`.
  `exactGlobalComplexHomologyIso` identifies its cohomology in degree `q` with
  `exactGlobalDerived q`, and `isZero_exactGlobalComplex_homology` gives vanishing in
  negative degrees.
- `exactInvariantGlobalComplex J R incl`: `DerivedPlus.derivedComplex` of
  `exactInvariantGlobalSections`, the complex `RΓ(X(G), incl F)` in
  `DerivedCategory.Plus (ModuleCat R)`. `exactInvariantGlobalComplexHomologyIso`
  identifies its cohomology in degree `q` with `exactInvariantGlobalDerived q`, and
  `isZero_exactInvariantGlobalComplex_homology` gives vanishing in negative degrees.

## The comparison of complexes

- `exactRestrictionGlobalComparison J R incl`: the natural transformation from the derived
  complex of `exactRestriction ⋙ sheafSectionsModule J R X₀` to
  `exactRestriction ⋙ sheafSectionsComplex J R X₀`, both followed by
  `DerivedCategory.Plus.ι`. Its components are `derivedCompComparison` for the identity
  of `exactRestriction ⋙ sheafSectionsModule J R X₀`, applicable because the positive
  derived functors of `exactRestriction` vanish; naturality is
  `derivedCompComparison_naturality`.
- `exactGlobalComplexComparison J R incl`: the comparison
  `RΓ(X{G}, incl F) → RΓ(X₀, b^*F)` in `DerivedCategory (ModuleCat R)`, from
  `exactGlobalComplex ⋙ DerivedCategory.Plus.ι` followed by the derived functor of
  `smoothForget R G`, to `exactRestriction ⋙ sheafSectionsComplex J R X₀` followed by
  `DerivedCategory.Plus.ι`. It is the composite of
  `(derivedPostcompIso (exactGlobalSections J R incl) (smoothForget R G)).hom`,
  `derivedComplexMap (exactGlobalInclusion J R incl)` and
  `exactRestrictionGlobalComparison`.
- `exactGlobalInclusionRestrictionComparison_homology F n`: on cohomology in degree `n`,
  under the identifications `DerivedPlus.homologyIso`, the last two factors induce
  `(LeftExactHomology.derivedNatTrans (smoothForget R G) (exactGlobalSections J R incl) n).app F`
  followed by `(exactGlobalComparison J R incl n).app F`. The proof rewrites with
  `derivedCompComparison_homology` and `derivedComplexMap_homology`, then unfolds
  `baseChangeNatTrans` and cancels the inverse of `derivedNatTrans`.
- `exactGlobalComplexComparison_homology_eq F n`: the degree `n` cohomology of
  `exactGlobalComplexComparison`, followed by `DerivedPlus.homologyIso` for the target,
  equals `mapDerivedCategoryHomologyIso (smoothForget R G) n`, then `smoothForget`
  applied to `DerivedPlus.homologyIso` for the source, then
  `exactGlobalComparison J R incl n`. The proof: `derivedCompIso` for the identity
  isomorphism is `derivedPostcompIso`; `derivedCompIso_hom_homology` computes the
  cohomology of the first factor up to the classical comparison
  `rightDerivedCompIsoOfResolution`; the previous theorem treats the other two factors;
  and `rightDerivedCompIsoOfResolution_refl_hom_comp_derivedNatTrans` cancels the
  classical comparison against `derivedNatTrans`.
- `exactGlobalComplexForgetHomologyIso F n`: the degree `n` cohomology of the image of
  `RΓ(X{G}, incl F)` under the derived `smoothForget` is the module underlying
  `exactGlobalDerived n`: `mapDerivedCategoryHomologyIso` followed by `smoothForget`
  applied to `exactGlobalComplexHomologyIso`.
- `exactGlobalComplexComparison_homology F n`: the same identity as the previous theorem
  with the target identified by `sheafSectionsComplexHomologyIso` and the source by
  `exactGlobalComplexForgetHomologyIso`; it is a regrouping.

So, after these identifications, `exactGlobalComplexComparison` induces in every degree
`n ≥ 0` the map `exactGlobalComparison J R incl n`. It is not proved that these maps are
isomorphisms.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (folder
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).

- §1.2, printed pp.4–5 = PDF pp.4–5: "The high direct images of the functor `Γ_{X{G}}` on
  the category of abelian sheaves will be denoted by `H^q(X{G}, F)`. For any abelian sheaf
  `F` there is a spectral sequence `E_2^{p,q} = H^p(G, H^q(X{G}, F)) ⟹ H^{p+q}(X(G), F)`."
  The functors `Γ_{X(G)}` and `Γ_{X{G}}` and their derived functors `H^q(X(G), F)` and
  `H^q(X{G}, F)` are quoted in full in the Markdown of `AnalyticEtaleCohomology`.
- Theorem 1.6.1(ii), printed p.13 = PDF p.13: "if `X` is compact, then for any
  quasi-étale (resp. étale) abelian sheaf `F` on `X(G)` one has
  `H^q(X{G}, F) ⥲ H^q(X, b^*F)` and, in particular, there is a spectral sequence
  `E_2^{p,q} = H^p(G, H^q(X, b^*F)) ⟹ H^{p+q}(X(G), F)`".

## Provenance and correspondence

Derived infrastructure. The correspondence with Berkovich is the one recorded in
`TwistedExactGlobalComparison`: `exactGlobalDerived q` has the shape of `H^q(X{G}, F)`,
`exactInvariantGlobalDerived q` that of `H^q(X(G), F)`, `exactRestriction` the role of
`b^*`, and `exactGlobalComparison q` the shape of the map of Theorem 1.6.1(ii) in degree
`q`. Berkovich works with cohomology groups and spectral sequences. The complexes
`exactGlobalComplex` (`RΓ(X{G}, F)`), `exactInvariantGlobalComplex` (`RΓ(X(G), F)`) and
`sheafSectionsComplex` (`RΓ(X, F)`), and the map of complexes, are our packaging. Their
definitions and proofs are those of the compact case in `TwistedExactCompactComparison`,
with `sheafSectionsModule` in place of `sheafCompactSections` and `exactGlobalInclusion`
in place of `exactCompactInclusion`.

## Not formalized here

That the comparison maps are isomorphisms; the spectral sequences of §1.2 and
Theorem 1.6.1(ii), and any identification of `RΓ(X(G), F)` with derived `G`-invariants of
`RΓ(X{G}, F)`; and the identification of the degree-zero comparison with
`exactGlobalInclusion`.
