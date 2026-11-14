# Invariant cohomology and derived global section complexes in the quasi-étale case

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.TwistedExactGlobalComplex` (Worker 26, submitted together
  with this module): the complexes `sheafSectionsComplex`, `exactGlobalComplex` and
  `exactInvariantGlobalComplex`, the comparison `exactGlobalComplexComparison` and the
  identifications of their cohomology. Through it, `TwistedExactGlobalComparison`
  (Worker 26): `exactInvariantGlobalSections`, `exactInvariantGlobalDerived`,
  `exactInvariantGlobalEdgeMap` and `isIso_exactInvariantGlobalEdgeMap_zero`.
- `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCohomology` (Worker 26):
  `quasiEtaleCohomology` (`H^q(X, F)` on the quasi-étale site), `quasiEtaleGSheafSections`
  (`Γ_{X{G}}`), `quasiEtaleGSheafCohomology` (`H^q(X{G}, F)`) and `quasiEtaleComparison`
  (`H^q(X{G}, F) → H^q(X, b^*F)`). Through it: `AnalyticQuasiEtaleComparison`
  (`quasiEtaleSelf`, `quasiEtale_enoughInjectives`, the restriction
  `quasiEtaleGSheafRestriction`, Berkovich's `b^*`), `AnalyticQuasiEtaleCompactCohomology`
  (`quasiEtale_hasSheafify`, `twistedQuasiEtale_hasSheafify`,
  `twistedQuasiEtale_enoughInjectives`), `TwistedGlobalSections` (`discreteGlobalSections`,
  `discreteGlobalDerived`, `globalComparison`), `LocalActionDiscretePart` (the abelian
  structure and enough injectives of discrete sheaves and the exactness of their inclusion
  `discreteSheafInclusion`), `AnalyticGSheaves` (`QuasiEtaleGSheaf ρ`, the discrete sheaves
  of `compactLiftSystem ρ`) and Worker 21's quasi-étale site with its topology
  `quasiEtaleTopology`.
- `Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtale`:
  `quasiEtale_hasPointwiseRightKanExtension`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.Analytic`.

## Purpose

`AnalyticQuasiEtaleCohomology` defines, for quasi-étale `G`-sheaves, `H^q(X{G}, F)` and the
comparison with `H^q(X, b^*F)` of Berkovich's Theorem 1.6.1(ii), but not `H^q(X(G), F)`,
which is the abutment of the spectral sequences of §1.2 and Theorem 1.6.1(ii). This module
adds `Γ_{X(G)}`, `H^q(X(G), F)` and the edge map, as `AnalyticEtaleCohomology` does in the
étale case. It also adds the complexes `RΓ(X, F)`, `RΓ(X{G}, F)` and `RΓ(X(G), F)` and the
comparison `RΓ(X{G}, F) → RΓ(X, b^*F)`, as `AnalyticEtaleGlobalComplex` does in the étale
case. Worker 16's published `AnalyticQuasiEtaleGlobalComparisonStatement` states that
`quasiEtaleComparison` is an isomorphism for compact `X`;
`quasiEtaleComplexComparison_homology` identifies the cohomology of the comparison of
complexes with `quasiEtaleComparison`.

## Data and universes

- `K : Type u` is a complete ultrametric normed field, and `X` an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`.
- Coefficients: write `w = max u (v + 1) uL`. The ring `R : Type w` is commutative, and
  sheaves take values in `ModuleCat.{w} R`. As `uL` occurs only inside `w`, uses name the
  universes explicitly, as in `quasiEtaleComplex.{u, v, uL} X R`. Sheafification, enough
  injectives and the Kan extension theorem are supplied locally with `haveI`.
- For quasi-étale `G`-sheaves: a topological group `G : Type z` and `ρ : G →* Aut X`. From
  left exactness on, the declarations assume `[Small.{w} G]` and
  `[(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]`,
  as in `AnalyticQuasiEtaleCohomology`.
- The derived categories of smooth representations and of modules are chosen by
  `[HasDerivedCategory.{w₃} (SmoothRep.{w, z, w} R G)]` and
  `[HasDerivedCategory.{w₄} (ModuleCat.{w} R)]`. The derived categories of module sheaves
  on the quasi-étale site and of quasi-étale `G`-sheaves are Mathlib's standard ones
  (`HasDerivedCategory.standard`), fixed inside the definitions, as for the compactly
  supported complexes in `AnalyticQuasiEtaleCompactCohomology` and
  `AnalyticQuasiEtaleComparison`. Different choices give canonically isomorphic objects;
  this is not formalized.

Throughout, `incl` is `(compactLiftSystem ρ).discreteSheafInclusion _ _` and
`J = quasiEtaleTopology X`. The published quasi-étale constructions use the discrete-sheaf
versions of `TwistedGlobalSections`; they agree definitionally with the generic ones for
`incl`: `discreteGlobalSections` is `incl ⋙ sheafGlobalSectionsSmooth`, which is
`exactGlobalSections` for `incl`, and `quasiEtaleGSheafRestriction` is `exactRestriction`
for `incl` after unfolding. The statements below that mention `quasiEtaleGSheafCohomology`,
`quasiEtaleGSheafRestriction` or `quasiEtaleComparison` typecheck by this unfolding.

## Module sheaves on the quasi-étale site

- `quasiEtaleComplex X R`: the complex `RΓ(X, F)` in `DerivedCategory.Plus (ModuleCat R)`,
  `sheafSectionsComplex` at `quasiEtaleSelf X`.
- `quasiEtaleComplexHomologyIso X R F q`: its cohomology in degree `q` is `H^q(X, F)`
  (`quasiEtaleCohomology X R q`).
- `isZero_quasiEtaleComplex_homology`: no cohomology in negative degrees.

## Invariant cohomology of quasi-étale `G`-sheaves

- `quasiEtaleGSheafInvariantSections ρ R`: Berkovich's `Γ_{X(G)}`, modelled as the
  `G`-invariant vectors of `Γ_{X{G}}` (`exactInvariantGlobalSections`). Additive
  (instance). `quasiEtaleGSheafInvariantSections_eq` (`rfl`): it is
  `quasiEtaleGSheafSections ρ R ⋙ smoothInvariantsFunctor R G`.
- `quasiEtaleGSheafInvariantSections_preservesFiniteLimits`: `Γ_{X(G)}` is left exact.
- `quasiEtaleGSheafInvariantCohomology ρ R q`: Berkovich's `H^q(X(G), F)`, the right
  derived functors of `Γ_{X(G)}` computed with injective resolutions among quasi-étale
  `G`-sheaves (`exactInvariantGlobalDerived`).
  `quasiEtaleGSheafInvariantCohomologyZeroIso ρ R`: `H^0(X(G), -) ≅ Γ_{X(G)}`.
- `quasiEtaleGlobalInvariantEdgeMap ρ R q`: the edge map `H^q(X(G), F) → H^q(X{G}, F)^G`,
  a natural transformation to
  `quasiEtaleGSheafCohomology ρ R q ⋙ smoothInvariantsFunctor R G`
  (`exactInvariantGlobalEdgeMap`). `isIso_quasiEtaleGlobalInvariantEdgeMap_zero`: it is an
  isomorphism in degree zero.

## Complexes of quasi-étale `G`-sheaves

- `quasiEtaleGSheafComplex ρ R`: Berkovich's `RΓ(X{G}, F)` in
  `DerivedCategory.Plus (SmoothRep R G)` (`exactGlobalComplex`).
  `quasiEtaleGSheafComplexHomologyIso ρ R F q`: its cohomology in degree `q` is
  `H^q(X{G}, F)` (`quasiEtaleGSheafCohomology ρ R q`).
  `isZero_quasiEtaleGSheafComplex_homology`: no cohomology in negative degrees.
- `quasiEtaleGSheafInvariantComplex ρ R`: Berkovich's `RΓ(X(G), F)` in
  `DerivedCategory.Plus (ModuleCat R)` (`exactInvariantGlobalComplex`).
  `quasiEtaleGSheafInvariantComplexHomologyIso ρ R F q`: its cohomology in degree `q` is
  `H^q(X(G), F)`. `isZero_quasiEtaleGSheafInvariantComplex_homology`: no cohomology in
  negative degrees.
- `quasiEtaleComplexComparison ρ R`: the comparison `RΓ(X{G}, F) → RΓ(X, b^*F)` in the
  derived category of modules (`exactGlobalComplexComparison`), from
  `quasiEtaleGSheafComplex ρ R ⋙ DerivedCategory.Plus.ι` followed by the derived functor
  of `smoothForget R G`, to `quasiEtaleGSheafRestriction ρ R` followed by
  `quasiEtaleComplex X R` and `DerivedCategory.Plus.ι`.
- `quasiEtaleComplexForgetHomologyIso ρ R F q`: the degree `q` cohomology of the source is
  the module underlying `H^q(X{G}, F)`.
- `quasiEtaleComplexComparison_homology ρ R F q`: on cohomology in degree `q`, through
  `quasiEtaleComplexForgetHomologyIso` and `quasiEtaleComplexHomologyIso`, the comparison
  of complexes is `(quasiEtaleComparison ρ R q).app F`.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (folder
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).
The passages are those quoted in full in the Markdown of `AnalyticEtaleCohomology`:

- §1.2, printed pp.4–5 = PDF pp.4–5: `Γ_{X(G)}`, the global sections functor on
  `X(G)~_qét` (resp. `X(G)~_ét`), and `Γ_{X{G}}`, with their high direct images
  `H^q(X(G), F)` and `H^q(X{G}, F)`; the identity `Γ_{X{G}}(F)^N = F(X_{G/N}(G))` for open
  subgroups `N`; and the spectral sequence
  `E_2^{p,q} = H^p(G, H^q(X{G}, F)) ⟹ H^{p+q}(X(G), F)`.
- Theorem 1.6.1(ii), printed p.13 = PDF p.13: for compact `X` and quasi-étale (resp.
  étale) `F`, `H^q(X{G}, F) ⥲ H^q(X, b^*F)` and the spectral sequence
  `E_2^{p,q} = H^p(G, H^q(X, b^*F)) ⟹ H^{p+q}(X(G), F)`.

## Provenance and correspondence

Specialization of derived infrastructure to the quasi-étale case. The modelling of
Berkovich's quasi-étale sheaves on `X(G)` by `QuasiEtaleGSheaf ρ`, of `Γ_{X{G}}` and of
`b^*` is the one recorded in the Markdown of `AnalyticQuasiEtaleCohomology`. As in the
étale case (Markdown of `AnalyticEtaleCohomology`), `Γ_{X(G)}` is modelled as the
`G`-invariant vectors of `Γ_{X{G}}`; for `N = G` Berkovich's identity reads
`Γ_{X{G}}(F)^G = F(X(G))`. Derived functors are taken among quasi-étale `G`-sheaves of
`R`-modules rather than among all quasi-étale abelian sheaves on `X(G)`; that they agree
with Berkovich's is not formalized. The edge map has the shape of the edge map
`H^q(X(G), F) → E_2^{0,q}` of the spectral sequence of §1.2, read as a composite-functor
spectral sequence for `Γ_{X(G)} = (-)^G ∘ Γ_{X{G}}`; this reading is ours. Berkovich works
with cohomology groups and spectral sequences; the complexes and the map of complexes are
our packaging.

## Not formalized here

That the comparison is an isomorphism for compact `X` (Theorem 1.6.1(ii), stated by
Worker 16 as `AnalyticQuasiEtaleGlobalComparisonStatement`, not proved); the spectral
sequences of §1.2 and Theorem 1.6.1(ii) and the identification of the edge map with
theirs; an identification of `RΓ(X(G), F)` with derived `G`-invariants of `RΓ(X{G}, F)`;
independence of the chosen derived categories; the comparison with the étale
constructions; and the refinement hypothesis, which remains a hypothesis.
