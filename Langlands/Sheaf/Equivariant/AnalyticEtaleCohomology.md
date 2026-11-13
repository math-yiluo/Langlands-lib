# Cohomology of étale sheaves and étale `G`-sheaves

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.TwistedExactGlobalComparison` (Worker 26, submitted
  together with this module): for an exact abelian subcategory `𝒜` of module sheaves on a
  twisted site, the smooth global sections `exactGlobalSections`, the invariant global
  sections `exactInvariantGlobalSections`, their derived functors `exactGlobalDerived`
  and `exactInvariantGlobalDerived`, the inclusion `exactGlobalInclusion`, the edge map
  `exactInvariantGlobalEdgeMap` and the comparison `exactGlobalComparison`. Through it,
  `TwistedGlobalSections` (Worker 26): `sheafSectionsModule` and `sectionsDerived`,
  sections over an object of an arbitrary site and their derived functors.
- `Langlands.Sheaf.Equivariant.AnalyticEtaleComparison` (Worker 26): the object
  `etaleSelf X` (the identity of `X` in its étale site), enough injectives for module
  sheaves on the étale site (`etale_enoughInjectives`), the Kan extension theorem
  `etale_hasPointwiseRightKanExtension`, and Berkovich's restriction `b^*` on étale
  `G`-sheaves (`etaleGSheafRestriction`). Through it: `AnalyticEtaleCompactCohomology`
  (sheafification on the étale and twisted étale sites, `etaleGSheaf_enoughInjectives`),
  `LocalActionSmoothPart` (the abelian structure of locally discrete sheaves and the
  exactness of their inclusion `smoothSheafInclusion`), `AnalyticGSheaves`
  (`EtaleGSheaf ρ`, the locally discrete sheaves of `distinguishedLiftSystem ρ` on the
  twisted étale site) and Worker 21's étale site `EtaleSite` with its topology
  `etaleTopology`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.Analytic`.

## Purpose

The Library has Berkovich's compactly supported cohomology `H^q_c(X{G}, -)` of étale
`G`-sheaves (`AnalyticEtaleCompactCohomology`) and the compactly supported comparison of
his Corollary 1.5.2(i) (`AnalyticEtaleComparison`). Both take supports in the `L`-valued
points of `X`, and the Markdown of `AnalyticEtaleComparison` explains why the comparison
is then not an isomorphism in general. Berkovich's Theorem 1.6.1(ii) compares instead,
for compact `X`, the ordinary cohomology: `H^q(X{G}, F) ≅ H^q(X, b^*F)` for quasi-étale
and for étale sheaves. The published `AnalyticQuasiEtaleCohomology` defines both sides
and the map for the quasi-étale case. This module does the same for the étale case, and
adds the invariant cohomology `H^q(X(G), F)` with its edge map. No points are involved.

## Data and universes

- `K : Type u` is a complete ultrametric normed field, and `X` an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`.
- Coefficients: write `w = max u (v + 1) uL`. The ring `R : Type w` is commutative, and
  sheaves take values in `ModuleCat.{w} R`. As `uL` occurs only inside `w`, uses name
  the universes explicitly, as in `etaleCohomology.{u, v, uL} X R q`. For the same
  reason the sheafification, injectivity and Kan extension facts are theorems, supplied
  locally with `haveI`, as in `AnalyticEtaleComparison`.
- For étale `G`-sheaves: a topological group `G : Type z` (`[TopologicalSpace G]`,
  `[IsTopologicalGroup G]`) and `ρ : G →* Aut X`. Smooth representations are
  `SmoothRep.{w, z, w} R G`. From exactness on, the declarations also assume
  `[Small.{w} G]` and
  `[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]`, as in
  `AnalyticEtaleCompactCohomology`. Worker 26's module `AnalyticEtaleRefinements` derives
  the second from three conditions on distinguished étale objects; this module does not
  import it.

## Module sheaves on the étale site

- `etaleSections X R`: `Γ(X, F)`, the sections over `etaleSelf X` of module sheaves on
  the étale site (`sheafSectionsModule`). It is additive and left exact (instances).
- `etaleCohomology X R q`: `H^q(X, F)`, the right derived functors of `Γ(X, -)`
  (`sectionsDerived`), computed with injective resolutions of module sheaves.
  Sheafification (`etale_hasSheafify`) and enough injectives (`etale_enoughInjectives`)
  are proved, so no hypothesis is needed.
- `etaleCohomologyZeroIso X R`: `H^0(X, -) ≅ Γ(X, -)`.
- `isZero_etaleCohomology_succ_of_injective`: `H^{q+1}(X, F) = 0` for injective `F`.

## Étale `G`-sheaves

Throughout, `incl` is `(distinguishedLiftSystem ρ).smoothSheafInclusion _ _`, the
inclusion of `EtaleGSheaf ρ (ModuleCat R)` into module sheaves on the twisted étale site,
and the generic declarations are applied with `J = etaleTopology X`. Their target
`sheafSectionsModule (etaleTopology X) R (base etale ρ).obj` is `etaleSections X R`,
because `etaleSelf X` is definitionally `(base etale ρ).obj`.

Without the size and refinement hypotheses:

- `etaleGSheafSections ρ R`: Berkovich's `Γ_{X{G}}`, the smooth part of the
  representation of `G` on the global sections of an étale `G`-sheaf
  (`exactGlobalSections`). Additive (instance).
- `etaleGlobalInclusion ρ R`: the inclusion `Γ_{X{G}}(F) → Γ(X, b^*F)`, a natural
  transformation from `etaleGSheafSections ρ R ⋙ smoothForget R G` to
  `etaleGSheafRestriction ρ R ⋙ etaleSections X R` (`exactGlobalInclusion`). By
  `etaleGlobalInclusion_app_apply` (`rfl`) it sends a smooth global section to itself.
- `etaleGSheafInvariantSections ρ R`: Berkovich's `Γ_{X(G)}`, modelled as the
  `G`-invariant vectors of `Γ_{X{G}}` (`exactInvariantGlobalSections`). Additive
  (instance).

With `[Small.{w} G]` and the refinement hypothesis, and with the sheafification on the
twisted étale site supplied by `haveI` in the statements that need it:

- `etaleGSheafSections_preservesFiniteLimits` and
  `etaleGSheafInvariantSections_preservesFiniteLimits`: `Γ_{X{G}}` and `Γ_{X(G)}` are left
  exact.
- `etaleGSheafCohomology ρ R q`: Berkovich's `H^q(X{G}, F)` as smooth representations of
  `G`, the right derived functors of `Γ_{X{G}}` computed with injective resolutions among
  étale `G`-sheaves (`exactGlobalDerived`).
  - `etaleGSheafCohomologyZeroIso ρ R`: `H^0(X{G}, -) ≅ Γ_{X{G}}`.
  - `etaleGSheafCohomologyIso I q`: for an injective resolution `I` of `F` among étale
    `G`-sheaves, `H^q(X{G}, F)` is the degree `q` cohomology of `Γ_{X{G}}` applied to `I`.
  - `isZero_etaleGSheafCohomology_succ_of_injective`: `H^{q+1}(X{G}, F) = 0` for `F`
    injective among étale `G`-sheaves.
- `etaleGSheafInvariantCohomology ρ R q`: Berkovich's `H^q(X(G), F)`, the right derived
  functors of `Γ_{X(G)}` computed with injective resolutions among étale `G`-sheaves
  (`exactInvariantGlobalDerived`). `etaleGSheafInvariantCohomologyZeroIso ρ R`:
  `H^0(X(G), -) ≅ Γ_{X(G)}`.
- `etaleGlobalInvariantEdgeMap ρ R q`: the edge map `H^q(X(G), F) → H^q(X{G}, F)^G`, a
  natural transformation to `etaleGSheafCohomology ρ R q ⋙ smoothInvariantsFunctor R G`
  (`exactInvariantGlobalEdgeMap`). `isIso_etaleGlobalInvariantEdgeMap_zero`: it is an
  isomorphism in degree zero.
- `etaleComparison ρ R q`: the comparison `H^q(X{G}, F) → H^q(X, b^*F)`
  (`exactGlobalComparison`), the base change of `etaleGlobalInclusion` along the exact
  functors `b^*` and `smoothForget`. Its source is
  `etaleGSheafCohomology ρ R q ⋙ smoothForget R G`, the underlying modules of
  `H^q(X{G}, F)`. Its target is `etaleGSheafRestriction ρ R ⋙ etaleCohomology X R q`.
  Sheafification and enough injectives on both sites and
  `etale_hasPointwiseRightKanExtension` are supplied by `haveI`; the exactness of `incl`
  comes from `LocalActionSmoothPart`.

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
  through open subgroups of `G`." Further: "for any open subgroup `N ⊂ G` one has
  `Γ_{X{G}}(F)^N = F(X_{G/N}(G))`. The high direct images of the functor `Γ_{X{G}}` on the
  category of abelian sheaves will be denoted by `H^q(X{G}, F)`. For any abelian sheaf `F`
  there is a spectral sequence `E_2^{p,q} = H^p(G, H^q(X{G}, F)) ⟹ H^{p+q}(X(G), F)`."
- Definition 1.4.1 and Theorem 1.4.2, printed pp.7–8: étale `G`-sheaves and the
  equivalence `X(G)~_ét ⥲ T_G(X_ét)` induced by `b : X → X(G)`. Definition 1.4.1 is
  quoted in the Markdown of `AnalyticEtaleComparison`, Theorem 1.4.2 in that of
  `AnalyticEtaleCompactCohomology`.
- Theorem 1.6.1, printed p.13 = PDF p.13: "Let `X` be a `G`-space. Then [...] (ii) if `X`
  is compact, then for any quasi-étale (resp. étale) abelian sheaf `F` on `X(G)` one has
  `H^q(X{G}, F) ⥲ H^q(X, b^*F)` and, in particular, there is a spectral sequence
  `E_2^{p,q} = H^p(G, H^q(X, b^*F)) ⟹ H^{p+q}(X(G), F)`".

## Provenance and correspondence

This module specializes derived infrastructure. The correspondence with Berkovich is the
one recorded in `TwistedExactGlobalComparison`, `AnalyticEtaleCompactCohomology` and
`AnalyticEtaleComparison`:

- Berkovich's étale abelian sheaves on `X(G)` are modelled by `EtaleGSheaf ρ`, the twisted
  model of `T_G(X_ét)`, through Theorem 1.4.2, which is not formalized.
- `Γ_{X{G}}` is the smooth part of the global sections representation, and `Γ_{X(G)}` its
  `G`-invariant vectors; for `N = G`, Berkovich's identity
  `Γ_{X{G}}(F)^N = F(X_{G/N}(G))` reads `Γ_{X{G}}(F)^G = F(X(G))`. `b^*` is restriction to
  the étale site of `X`. `H^q(X, -)` is computed on the étale site of `X`, as in the étale
  case of Theorem 1.6.1.
- Berkovich takes derived functors on all étale abelian sheaves on `X(G)`. Here they are
  taken among étale `G`-sheaves of `R`-modules, `R : Type w`; the case of abelian sheaves
  is `R = ULift ℤ`. That these derived functors agree with Berkovich's is not formalized.
- The comparison is the base change of the inclusion `Γ_{X{G}}(F) ⊆ (b^*F)(X)`. That it is
  an isomorphism for compact `X` (Theorem 1.6.1(ii)) is not proved, and no compactness
  hypothesis on `X` appears in these declarations.
- `etaleGlobalInvariantEdgeMap` has the shape of the edge map `H^q(X(G), F) → E_2^{0,q}` of
  the spectral sequence of §1.2, read as a composite-functor spectral sequence for
  `Γ_{X(G)} = (-)^G ∘ Γ_{X{G}}`. This reading is ours.

## Not formalized here

Theorem 1.6.1 and its spectral sequences; the spectral sequence of §1.2 and the
identification of `etaleGlobalInvariantEdgeMap` with its edge map; the degree-zero
identification of `etaleComparison` with `etaleGlobalInclusion`; Theorem 1.4.2; the
comparison with the quasi-étale constructions of `AnalyticQuasiEtaleCohomology`; and the
refinement hypothesis, which remains a hypothesis.
