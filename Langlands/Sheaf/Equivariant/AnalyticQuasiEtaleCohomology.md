# Cohomology of quasi-étale sheaves and quasi-étale `G`-sheaves

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.TwistedGlobalSections` (Worker 26, submitted together with
  this module): sections over an object and their derived functors on an arbitrary site,
  and the smooth global sections `discreteGlobalSections`, their derived functors
  `discreteGlobalDerived`, the inclusion `smoothGlobalInclusion` and the comparison
  `globalComparison` on an arbitrary twisted site.
- `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleComparison` (Worker 26): the object
  `quasiEtaleSelf X` (the identity of `X` in its quasi-étale site), enough injectives for
  module sheaves on the quasi-étale site (`quasiEtale_enoughInjectives`), and Berkovich's
  restriction `b^*` on quasi-étale `G`-sheaves (`quasiEtaleGSheafRestriction`). Through it:
  `AnalyticQuasiEtaleCompactCohomology` (sheafification on both sites, enough injectives on
  the twisted site), `AnalyticQuasiEtale` (the Kan extension instance
  `quasiEtale_hasPointwiseRightKanExtension`), `AnalyticGSheaves` (`QuasiEtaleGSheaf ρ`, the
  discrete sheaves of `compactLiftSystem ρ` on the twisted quasi-étale site) and Worker 21's
  quasi-étale site.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.Analytic`.

## Purpose

The Library has Berkovich's compactly supported cohomology `H^q_c(X{G}, -)` of quasi-étale
`G`-sheaves (`AnalyticQuasiEtaleCompactCohomology`) and the compactly supported comparison
of his Corollary 1.5.2 (`AnalyticQuasiEtaleComparison`). Both take supports in the
`L`-valued points of `X`. On the Library's quasi-étale model that comparison fails to be an
isomorphism for some sheaves on a noncompact `X` (Worker 16's example in
`notes/henniart/harris-cohomology-coverage.md`, section "Retained source gaps and scope
decisions"). For compact `X`, Berkovich's Theorem 1.6.1(ii) compares instead the ordinary
cohomology: `H^q(X{G}, F) ≅ H^q(X, b^*F)` for quasi-étale sheaves. This module defines both
sides and the comparison map. No points are involved.

## Data and universes

- `K : Type u` is a complete ultrametric normed field, and `X` an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`.
- Coefficients: write `w = max u (v + 1) uL`. The ring `R : Type w` is commutative. The
  universe `w` is the one of the published sheafification and injectivity results. As
  `uL` occurs only inside `w`, uses name the universes explicitly, as in
  `quasiEtaleCohomology.{u, v, uL} X R q`.
- For quasi-étale `G`-sheaves: a topological group `G : Type z` with `[IsTopologicalGroup G]`
  and `ρ : G →* Aut X`. The cohomology and the comparison also assume `[Small.{w} G]` and
  `[(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]`,
  as in `AnalyticQuasiEtaleCompactCohomology`. The second is not proved in general.

## Module sheaves on the quasi-étale site

- `quasiEtaleSections X R`: `Γ(X, F)`, the sections over `quasiEtaleSelf X` of module sheaves
  on the quasi-étale site (`sheafSectionsModule`). It is additive and left exact.
- `quasiEtaleCohomology X R q`: `H^q(X, F)`, the right derived functors of `Γ(X, -)`
  (`sectionsDerived`). Sheafification (`quasiEtale_hasSheafify`) and enough injectives
  (`quasiEtale_enoughInjectives`) are proved, so no hypothesis is needed.
- `quasiEtaleCohomologyZeroIso X R`: `H^0(X, -) ≅ Γ(X, -)`.
- `isZero_quasiEtaleCohomology_succ_of_injective`: `H^{q+1}(X, F) = 0` for injective `F`.

## Quasi-étale `G`-sheaves

- `quasiEtaleGSheafSections ρ R`: Berkovich's `Γ_{X{G}}`, the smooth part of the
  representation of `G` on the global sections of a quasi-étale `G`-sheaf
  (`discreteGlobalSections`). It is additive, and left exact
  (`quasiEtaleGSheafSections_preservesFiniteLimits`, stated with the sheafification on the
  twisted site supplied by `haveI`).
- `quasiEtaleGlobalInclusion ρ R`: the inclusion `Γ_{X{G}}(F) → Γ(X, b^*F)`
  (`smoothGlobalInclusion`). By `quasiEtaleGlobalInclusion_app_apply` (`rfl`) it sends a
  smooth global section to itself.
- `quasiEtaleGSheafCohomology ρ R q`: Berkovich's `H^q(X{G}, F)` as smooth representations
  of `G`, the right derived functors of `Γ_{X{G}}` computed with injective resolutions among
  quasi-étale `G`-sheaves (`discreteGlobalDerived`).
- `quasiEtaleGSheafCohomologyZeroIso ρ R`: `H^0(X{G}, -) ≅ Γ_{X{G}}`.
- `isZero_quasiEtaleGSheafCohomology_succ_of_injective`: `H^{q+1}(X{G}, F) = 0` for `F`
  injective among quasi-étale `G`-sheaves.
- `quasiEtaleComparison ρ R q`: the comparison
  `H^q(X{G}, F) → H^q(X, b^*F)`, the published `globalComparison`: the base change of
  `quasiEtaleGlobalInclusion` along the exact functors `b^*` and `smoothForget`. Its source
  is `quasiEtaleGSheafCohomology ρ R q ⋙ smoothForget R G`, the underlying modules of
  `H^q(X{G}, F)`. Its target is `quasiEtaleGSheafRestriction ρ R ⋙ quasiEtaleCohomology X R q`.

As in the other quasi-étale modules, the instances that the generic declarations need are
supplied locally with `haveI`.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (folder
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).

- §1.2, printed pp.4–5 = PDF pp.4–5: `Γ_{X(G)}(F) = F(X(G))`;
  "`Γ_{X{G}}(F) = lim_→ F(X_{G/N}(G))`, where `N` runs through open subgroups of `G`";
  "for any open subgroup `N ⊂ G` one has `Γ_{X{G}}(F)^N = F(X_{G/N}(G))`. The high direct
  images of the functor `Γ_{X{G}}` on the category of abelian sheaves will be denoted by
  `H^q(X{G}, F)`."
- Definition 1.4.1 and Theorem 1.4.2, printed pp.7–8: quasi-étale `G`-sheaves and the
  equivalence `X(G)~_qét ⥲ T_G(X_qét)` induced by `b : X → X(G)`. They are quoted in the
  Markdown of `AnalyticQuasiEtaleCompactCohomology`.
- Theorem 1.6.1, printed p.13 = PDF p.13: "Let `X` be a `G`-space. Then (i) if `X` is
  paracompact, then the values of the high direct images of the functor `F ↦ (b^*F)(X)` on
  the category of quasi-étale (resp. étale) abelian sheaves on `X(G)` are the cohomology
  groups `H^q(X, b^*F)`; (ii) if `X` is compact, then for any quasi-étale (resp. étale)
  abelian sheaf `F` on `X(G)` one has `H^q(X{G}, F) ⥲ H^q(X, b^*F)`".

## Provenance and correspondence

This module specializes derived infrastructure:

- Berkovich's quasi-étale sheaves on `X(G)` are modelled by quasi-étale `G`-sheaves
  `QuasiEtaleGSheaf ρ` through Theorem 1.4.2, as in `AnalyticQuasiEtaleCompactCohomology`.
  Theorem 1.4.2 is not formalized.
- `Γ_{X{G}}` is the smooth part of the global sections representation (see
  `TwistedGlobalSections`). `H^q(X, -)` is computed on the quasi-étale site of `X`, as in
  Theorem 1.6.1. The étale cohomology is not compared.
- Berkovich works with abelian sheaves; here sheaves take values in `R`-modules with
  `R : Type w`. The case of abelian sheaves is `R = ULift ℤ`. That the derived functors on
  `R`-module sheaves agree with those on abelian sheaves is not formalized.
- The comparison is the base change of the inclusion `Γ_{X{G}}(F) ⊆ (b^*F)(X)`. That it is an
  isomorphism for compact `X` (Theorem 1.6.1(ii)) is not proved. No compactness hypothesis
  on `X` appears in these declarations.

## Not formalized here

Theorem 1.6.1, its spectral sequence `H^p(G, H^q(X, b^*F)) ⇒ H^{p+q}(X(G), F)`, the
invariant cohomology `H^q(X(G), F)`, and the comparison with étale cohomology.
