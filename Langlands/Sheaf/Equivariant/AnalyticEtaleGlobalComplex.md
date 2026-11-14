# Derived global section complexes on the étale site and of étale `G`-sheaves

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.TwistedExactGlobalComplex` (Worker 26, submitted together
  with this module): for an exact abelian subcategory `𝒜` of module sheaves on a twisted
  site, the complexes `sheafSectionsComplex`, `exactGlobalComplex` and
  `exactInvariantGlobalComplex`, the comparison `exactGlobalComplexComparison` and the
  identifications of their cohomology.
- `Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology` (Worker 26): `etaleCohomology`
  (`H^q(X, F)` on the étale site), `etaleGSheafCohomology` (`H^q(X{G}, F)`),
  `etaleGSheafInvariantCohomology` (`H^q(X(G), F)`) and `etaleComparison`
  (`H^q(X{G}, F) → H^q(X, b^*F)`). Through it: `AnalyticEtaleComparison` (`etaleSelf`,
  `etale_enoughInjectives`, `etale_hasPointwiseRightKanExtension`, the restriction
  `etaleGSheafRestriction`, Berkovich's `b^*`), `AnalyticEtaleCompactCohomology`
  (`etale_hasSheafify`, `twistedEtale_hasSheafify`, `etaleGSheaf_enoughInjectives`),
  `LocalActionSmoothPart` (the abelian structure of locally discrete sheaves and the
  exactness of `smoothSheafInclusion`), `AnalyticGSheaves` (`EtaleGSheaf ρ`) and Worker
  21's étale site `EtaleSite` with its topology `etaleTopology`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.Analytic`.

## Purpose

The Library has the compactly supported complexes `RΓ_c(X, F)` and `RΓ_c(X{G}, F)` on the
étale site and the comparison of complexes `RΓ_c(X{G}, F) → RΓ_c(X, b^*F)`
(`AnalyticEtaleCompactCohomology`, `AnalyticEtaleComparison`). For ordinary cohomology it
has only the groups `H^q(X, F)`, `H^q(X{G}, F)`, `H^q(X(G), F)` and the comparison in each
degree (`AnalyticEtaleCohomology`). This module adds the complexes `RΓ(X, F)`,
`RΓ(X{G}, F)` and `RΓ(X(G), F)` and the comparison `RΓ(X{G}, F) → RΓ(X, b^*F)`, the
derived-category form of the input of Berkovich's §1.2 and Theorem 1.6.1(ii).

## Data and universes

- `K : Type u` is a complete ultrametric normed field, and `X` an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`.
- Coefficients: write `w = max u (v + 1) uL`. The ring `R : Type w` is commutative, and
  sheaves take values in `ModuleCat.{w} R`. As `uL` occurs only inside `w`, uses name the
  universes explicitly, as in `etaleComplex.{u, v, uL} X R`. Sheafification, enough
  injectives and the Kan extension theorem are supplied locally with `haveI`, as in
  `AnalyticEtaleCohomology`.
- For étale `G`-sheaves: a topological group `G : Type z` with `[Small.{w} G]`,
  `ρ : G →* Aut X`, and the hypothesis
  `[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]` of
  `AnalyticEtaleCompactCohomology`.
- The derived categories of smooth representations and of modules are chosen by
  `[HasDerivedCategory.{w₃} (SmoothRep.{w, z, w} R G)]` and
  `[HasDerivedCategory.{w₄} (ModuleCat.{w} R)]`. The derived categories of module sheaves
  on the étale site and of étale `G`-sheaves are Mathlib's standard ones
  (`HasDerivedCategory.standard`), fixed inside the definitions, as for the compactly
  supported complexes in `AnalyticEtaleCompactCohomology` and `AnalyticEtaleComparison`.
  Different choices give canonically isomorphic objects; this is not formalized.

## Module sheaves on the étale site

- `etaleComplex X R`: the complex `RΓ(X, F)` in `DerivedCategory.Plus (ModuleCat R)`,
  `sheafSectionsComplex` at `etaleSelf X`.
- `etaleComplexHomologyIso X R F q`: its cohomology in degree `q` is `H^q(X, F)`
  (`etaleCohomology X R q`).
- `isZero_etaleComplex_homology`: no cohomology in negative degrees.

## Étale `G`-sheaves

Throughout, `incl` is `(distinguishedLiftSystem ρ).smoothSheafInclusion _ _` and
`J = etaleTopology X`.

- `etaleGSheafComplex ρ R`: Berkovich's `RΓ(X{G}, F)` in
  `DerivedCategory.Plus (SmoothRep R G)` (`exactGlobalComplex`).
  `etaleGSheafComplexHomologyIso ρ R F q`: its cohomology in degree `q` is
  `H^q(X{G}, F)` (`etaleGSheafCohomology ρ R q`). `isZero_etaleGSheafComplex_homology`:
  no cohomology in negative degrees.
- `etaleGSheafInvariantComplex ρ R`: Berkovich's `RΓ(X(G), F)` in
  `DerivedCategory.Plus (ModuleCat R)` (`exactInvariantGlobalComplex`).
  `etaleGSheafInvariantComplexHomologyIso ρ R F q`: its cohomology in degree `q` is
  `H^q(X(G), F)` (`etaleGSheafInvariantCohomology ρ R q`).
  `isZero_etaleGSheafInvariantComplex_homology`: no cohomology in negative degrees.
- `etaleComplexComparison ρ R`: the comparison `RΓ(X{G}, F) → RΓ(X, b^*F)` in the derived
  category of modules (`exactGlobalComplexComparison`). Its source is
  `etaleGSheafComplex ρ R ⋙ DerivedCategory.Plus.ι` followed by the derived functor of
  `smoothForget R G`; its target is `etaleGSheafRestriction ρ R` followed by
  `etaleComplex X R` and `DerivedCategory.Plus.ι`. The target matches that of the generic
  construction because `etaleSelf X` is definitionally `(base etale ρ).obj` and
  `etaleGSheafRestriction` is `exactRestriction` for `incl`.
- `etaleComplexForgetHomologyIso ρ R F q`: the degree `q` cohomology of the source is the
  module underlying `H^q(X{G}, F)`.
- `etaleComplexComparison_homology ρ R F q`: on cohomology in degree `q`, through
  `etaleComplexForgetHomologyIso` and `etaleComplexHomologyIso`, the comparison of
  complexes is `(etaleComparison ρ R q).app F`.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (folder
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).
The passages are those quoted in full in the Markdown of `AnalyticEtaleCohomology`:

- §1.2, printed pp.4–5 = PDF pp.4–5: `Γ_{X(G)}` and `Γ_{X{G}}` with their high direct
  images `H^q(X(G), F)` and `H^q(X{G}, F)`, and the spectral sequence
  `E_2^{p,q} = H^p(G, H^q(X{G}, F)) ⟹ H^{p+q}(X(G), F)`.
- Theorem 1.6.1(ii), printed p.13 = PDF p.13: for compact `X` and quasi-étale (resp.
  étale) `F`, `H^q(X{G}, F) ⥲ H^q(X, b^*F)` and the spectral sequence
  `E_2^{p,q} = H^p(G, H^q(X, b^*F)) ⟹ H^{p+q}(X(G), F)`.

## Provenance and correspondence

Specialization of derived infrastructure. The modelling of Berkovich's étale sheaves on
`X(G)` by `EtaleGSheaf ρ`, of `Γ_{X{G}}`, `Γ_{X(G)}` and `b^*`, and of derived functors
among étale `G`-sheaves of `R`-modules, is the one recorded in the Markdown of
`AnalyticEtaleCohomology`. Berkovich works with cohomology groups and spectral sequences;
the complexes and the map of complexes are our packaging of his derived functors, as for
compact supports in `AnalyticEtaleComparison`.

## Not formalized here

That the comparison is an isomorphism for compact `X` (Theorem 1.6.1(ii)); the spectral
sequences of §1.2 and Theorem 1.6.1(ii); an identification of `RΓ(X(G), F)` with derived
`G`-invariants of `RΓ(X{G}, F)`; independence of the chosen derived categories; and the
refinement hypothesis, which remains a hypothesis.
