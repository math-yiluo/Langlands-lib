# Equivariant and plain compactly supported cohomology on the quasi-étale site

Author: Worker 26. Uses Worker 26's published modules
`Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCompactCohomology` (essential smallness,
sheafification, the points `quasiEtalePoints L h`, and `Γ_{c,X{G}}`, `H^q_c(X{G}, F)` and
`RΓ_c(X{G}, F)` on quasi-étale `G`-sheaves),
`Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtale` (the right Kan extensions
`quasiEtale_hasPointwiseRightKanExtension`), `Langlands.Sheaf.PointSupport`
(`sheafCompactSections`, `compactDerived` on a site with points),
`Langlands.Cohomology.DiscreteSheafDerivedComplex` (`sheafCompactComplex`),
`Langlands.Sheaf.Equivariant.TwistedCompactComparison` (`smoothForget`,
`smoothCompactInclusion`, `discreteInvariantCompactSections`,
`discreteInvariantCompactDerived`, `invariantEdgeMap`, `compactComparison`),
`Langlands.Cohomology.DiscreteSheafDerivedComparison` (`discreteRestriction`, the
exactness of restriction, `compactComplexComparison`) and
`Langlands.Cohomology.DiscreteSheafDerivedComparisonHomology`
(`compactComplexForgetHomologyIso`, `compactComplexComparison_homology`). From Worker 21
it uses the quasi-étale site `QuasiEtaleSite`, its topology `quasiEtaleTopology`, the
action `EtaleSite.pointAction` of `G` on `L`-valued points and
`QuasiEtaleSite.pointEquivariance`.

## Purpose

`AnalyticQuasiEtaleCompactCohomology` defines `H^q_c(X{G}, F)` for Berkovich's
quasi-étale `G`-sheaves on a `K`-analytic space `X`. Berkovich compares it with the
compactly supported cohomology of the underlying sheaf on `X` (Corollary 1.5.2(i)). This
module defines the other objects of that statement on the quasi-étale site, and the maps
between them. They are the published constructions of `TwistedCompactComparison` and
`DiscreteSheafDerivedComparison`, specialized to the quasi-étale site. The module
defines:

- `Γ_c(X, -)`, `H^q_c(X, -)` and `RΓ_c(X, -)` for module sheaves on the quasi-étale site
  of `X`;
- Berkovich's `b^*`, the restriction from quasi-étale `G`-sheaves to sheaves on the
  quasi-étale site of `X`;
- `Γ_{c,X(G)}` and `H^q_c(X(G), F)` on quasi-étale `G`-sheaves, with the edge map
  `H^q_c(X(G), F) → H^q_c(X{G}, F)^G`;
- the comparison maps `H^q_c(X{G}, F) → H^q_c(X, b^*F)`, in each degree and as one map of
  complexes, and their compatibility on cohomology.

That the comparison maps are isomorphisms is not proved.

All declarations are in `Langlands.Sheaf.Equivariant.Analytic`.

## Data and universes

As in `AnalyticQuasiEtaleCompactCohomology`:

- `K : Type u` is a complete ultrametric normed field and `X` an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`.
- `L : Type uL` is a normed field with `[NormedAlgebra K L]`, and
  `h : ∀ x, QuasiEtaleSite.PointAxioms L x` is the hypothesis that every `L`-valued
  point of `X` satisfies Worker 21's point axioms.
- `G : Type z` is a group with `ρ : G →* Aut X`. From the section on comparison on,
  `[TopologicalSpace G] [IsTopologicalGroup G]`.
- `R : Type w` is a commutative ring, `w = max u (v + 1) uL`, and sheaves take values in
  `ModuleCat.{w} R`. Smooth representations are `SmoothRep.{w, z, w} R G`.
- Statements about the twisted site assume `[Small.{w} G]` and
  `[(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]`,
  the hypotheses of `AnalyticQuasiEtaleCompactCohomology`.

Some declarations carry the explicit universe list `.{u, v, uL}`. The universe `uL`
occurs in their types only inside `max u (v + 1) uL`, where Lean does not infer it.
The theorems below that state additivity, exactness or invertibility are not instances
for the reason given in `AnalyticQuasiEtaleCompactCohomology`: instance search does not
solve the universe constraints of `ModuleCat.{max u (v + 1) uL}`.

## Plain compactly supported cohomology on the quasi-étale site

No group appears in this section. The topology `pointTopology L X` on `L`-valued points,
the local smallness of `QuasiEtaleSite X` in `w` and sheafification
(`quasiEtale_hasSheafify`) come from `AnalyticQuasiEtaleCompactCohomology` and are
supplied locally.

- `quasiEtale_enoughInjectives X R`: module sheaves on the quasi-étale site of `X` have
  enough injectives. The site is essentially small in `w`, so Mathlib's
  `Sheaf.isGrothendieckAbelian_of_essentiallySmall` shows that the sheaf category is a
  Grothendieck abelian category, and `IsGrothendieckAbelian.enoughInjectives` concludes.
  The limits over `StructuredArrow Y (equivSmallModel _).inverse.op` that the first
  lemma needs exist by `hasLimitsOfShape_of_essentiallySmall`. The proof is the one of
  `twistedQuasiEtale_enoughInjectives`.
- `quasiEtaleSelf X`: `X` as an object of its quasi-étale site, by the identity. It is
  definitionally `(base quasiEtale ρ).obj` for every `ρ`.
- `quasiEtaleCompactSections L h R`: `Γ_c(X, F)`, the compactly supported global sections
  of a module sheaf `F`, with supports in the `L`-valued points. It is the published
  `sheafCompactSections` for the points `quasiEtalePoints L h` at `quasiEtaleSelf X`. It
  is additive (`quasiEtaleCompactSections_additive`).
- `quasiEtaleCompactCohomology L h R q`: `H^q_c(X, F)`, the published `compactDerived`,
  the right derived functors of `Γ_c(X, -)` computed with injective resolutions of
  module sheaves. `quasiEtaleCompactCohomologyZeroIso` identifies `H^0_c(X, -)` with
  `Γ_c(X, -)`.
- `quasiEtaleCompactComplex L h R`, with `[HasDerivedCategory.{w₄} (ModuleCat R)]`: the
  complex `RΓ_c(X, F)` in `DerivedCategory.Plus (ModuleCat R)`, the published
  `sheafCompactComplex`. The derived category of module sheaves it uses inside is
  Mathlib's `HasDerivedCategory.standard`, so no hypothesis about it is needed; the
  functor's value does not mention that choice.
  `quasiEtaleCompactComplexHomologyIso F q` identifies its cohomology in degree `q` with
  `H^q_c(X, F)`, and `isZero_quasiEtaleCompactComplex_homology` gives vanishing in
  negative degrees.

## The restriction `b^*`

- `quasiEtaleGSheafRestriction ρ R`: from `QuasiEtaleGSheaf ρ (ModuleCat R)` to module
  sheaves on the quasi-étale site of `X`. It is the published `discreteRestriction`: the
  inclusion of quasi-étale `G`-sheaves into sheaves on the twisted quasi-étale site,
  followed by restriction along the inclusion of the quasi-étale site of `X`, which
  forgets the action of `G`.
- `quasiEtaleGSheafRestriction_additive`: it is additive (`map_add` holds by `rfl`).
- `quasiEtaleGSheafRestriction_preservesFiniteLimits` and
  `quasiEtaleGSheafRestriction_preservesFiniteColimits` (with `[Small.{w} G]` and the
  finite equivariant refinements): it is exact. These are the published
  `discreteRestriction_preservesFiniteLimits` and
  `discreteRestriction_preservesFiniteColimits`. The latter rests on the restriction
  adjunction of `TwistedGodement`, whose right Kan extensions are
  `quasiEtale_hasPointwiseRightKanExtension`.

## Invariant cohomology and the comparison maps

In this section `G` is a topological group. The topology on `L`-valued points, Worker
21's action `EtaleSite.pointAction L ρ` with `continuousConstSMul_pointAction`, local
smallness, sheafification on both sites, enough injectives on both sites and the right
Kan extensions are supplied locally. The `TwistedOver.PointEquivariance` used throughout
is Worker 21's `QuasiEtaleSite.pointEquivariance L ρ h`, and the local action system is
`compactLiftSystem ρ`.

- `quasiEtaleCompactInclusion L ρ h R`: the inclusion
  `Γ_{c,X{G}}(F) → Γ_c(X, b^*F)`, a natural transformation from
  `quasiEtaleGSheafCompactSections L ρ h R ⋙ smoothForget R G` to
  `quasiEtaleGSheafRestriction ρ R ⋙ quasiEtaleCompactSections L h R`. It is the
  published `smoothCompactInclusion`, which sends a smooth compactly supported section to
  itself.
- `quasiEtaleGSheafInvariantCompactSections L ρ h R`: `Γ_{c,X(G)}`, the published
  `discreteInvariantCompactSections`. By `quasiEtaleGSheafInvariantCompactSections_eq`
  (`rfl`) it is `Γ_{c,X{G}}` followed by `smoothInvariantsFunctor R G`, the
  `G`-invariant vectors. The published `discreteInvariantCompactSectionsIso` identifies
  it with the `G`-invariant compactly supported global sections.

From here on `[Small.{w} G]` and the finite equivariant refinements are assumed.

- `quasiEtaleGSheafInvariantCompactCohomology L ρ h R q`: `H^q_c(X(G), F)`, the published
  `discreteInvariantCompactDerived`, the right derived functors of `Γ_{c,X(G)}` computed
  with injective resolutions among quasi-étale `G`-sheaves.
  `quasiEtaleGSheafInvariantCompactCohomologyZeroIso` identifies degree zero with
  `Γ_{c,X(G)}`.
- `quasiEtaleInvariantEdgeMap L ρ h R q`: the natural transformation
  `H^q_c(X(G), F) → H^q_c(X{G}, F)^G`, to `quasiEtaleGSheafCompactCohomology L ρ h R q`
  followed by `smoothInvariantsFunctor R G`. It is the published `invariantEdgeMap`, the
  comparison `LeftExactHomology.derivedNatTrans` for `Γ_{c,X{G}}` followed by the
  invariants. `isIso_quasiEtaleInvariantEdgeMap_zero`: it is an isomorphism in degree
  zero.
- `quasiEtaleCompactComparison L ρ h R q`: the comparison
  `H^q_c(X{G}, F) → H^q_c(X, b^*F)` in degree `q`, a natural transformation from
  `quasiEtaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G` to
  `quasiEtaleGSheafRestriction ρ R ⋙ quasiEtaleCompactCohomology L h R q`. It is the
  published `compactComparison`, the base change of `quasiEtaleCompactInclusion` along
  the exact functors `b^*` and `smoothForget`.

With `[HasDerivedCategory.{w₃} (SmoothRep R G)]` and
`[HasDerivedCategory.{w₄} (ModuleCat R)]`; the derived categories of quasi-étale
`G`-sheaves and of module sheaves used inside are Mathlib's standard ones, as for
`RΓ_c(X{G}, F)` in `AnalyticQuasiEtaleCompactCohomology`:

- `quasiEtaleCompactComplexComparison L ρ h R`: the comparison
  `RΓ_c(X{G}, F) → RΓ_c(X, b^*F)` in `DerivedCategory (ModuleCat R)`, a natural
  transformation from `quasiEtaleGSheafCompactComplex L ρ h R`, followed by
  `DerivedCategory.Plus.ι` and the derived functor of the exact functor `smoothForget R G`,
  to `quasiEtaleGSheafRestriction ρ R ⋙ quasiEtaleCompactComplex L h R` followed by
  `DerivedCategory.Plus.ι`. It is the published `compactComplexComparison`.
- `quasiEtaleCompactComplexForgetHomologyIso L ρ h R F q`: the cohomology in degree `q`
  of the image of `RΓ_c(X{G}, F)` under the derived `smoothForget` is the module
  underlying `H^q_c(X{G}, F)` (the published `compactComplexForgetHomologyIso`).
- `quasiEtaleCompactComplexComparison_homology L ρ h R F q`: on cohomology in degree `q`,
  the comparison of complexes, followed by
  `quasiEtaleCompactComplexHomologyIso` for `b^*F`, equals
  `quasiEtaleCompactComplexForgetHomologyIso` followed by `quasiEtaleCompactComparison`
  in degree `q` (the published `compactComplexComparison_homology`).

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (folder
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).

- §1.5, printed p.11 = PDF p.11: "Let F be an étale abelian sheaf on X(G). The support of
  an element f ∈ F(X(G)) is the set Supp(f) = {x ∈ X | f_x ≠ 0}, where f_x is the image of
  f in F_x. It is a closed subset of X. The values of the high direct images of the
  functor F ↦ Γ_{c,X(G)}(F) := {f ∈ F(X(G)) | Supp(f) is compact} are called the
  cohomology groups with compact support and denoted by H^q_c(X(G), F). The values of the
  high direct images of the functor F ↦ Γ_{c,X{G}}(F) := lim_→ Γ_{c,X(N)}(F), where N runs
  through open subgroups of G, are denoted by H^q_c(X{G}, F)."
- Corollary 1.5.2(i), printed pp.11–12: "For any étale abelian sheaf F on X(G) there are
  canonical isomorphisms H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F), g ≥ 0 [sic, for q ≥ 0]. In
  particular, the canonical action of G on the groups H^q_c(X, b^*F) is discrete and there
  is a spectral sequence E_2^{p,q} = H^p(G, H^q_c(X, b^*F)) ⟹ H^{p+q}_c(X(G), F)." The
  proof, printed p.12: "The case q = 0 in (i) (resp. (ii)) follows from the fact that every
  element of H^0_c(X, b^*F) is fixed by an open subgroup of G (resp. is trivial), and
  therefore the general case follows from Proposition 1.5.1."

## Provenance and correspondence

This module specializes derived infrastructure. The correspondence with Berkovich is the
one recorded in `TwistedCompactComparison` and `AnalyticQuasiEtaleCompactCohomology`. The
choices below are ours:

- Berkovich's statement is for étale abelian sheaves on `X(G)`. Here the source category
  is the quasi-étale `G`-sheaves `T_G(X_qét)`, as for `H^q_c(X{G}, F)` in
  `AnalyticQuasiEtaleCompactCohomology`, and `X` carries its quasi-étale site, so
  `H^q_c(X, b^*F)` is quasi-étale cohomology. The comparison with étale cohomology is not
  formalized.
- `b^*` is restriction of the twisted model to the quasi-étale site of `X`. Sections over
  `X(G)` are the `G`-invariant sections of the underlying sheaf (proof of Theorem 1.4.2,
  printed p.9), so `Γ_{c,X(G)}` is modelled by the `G`-invariant vectors of
  `Γ_{c,X{G}}`, which are the `G`-invariant compactly supported global sections.
- Berkovich takes the derived functors of `Γ_{c,X(G)}` on all étale abelian sheaves on
  `X(G)`. Here they are taken among quasi-étale `G`-sheaves.
- Supports are taken in the `L`-valued points with the topology induced from `|X|`, as in
  `AnalyticCompactSupport`, and the point axioms are a hypothesis.
- In degree zero, the comparison map of Corollary 1.5.2(i) is the inclusion
  `quasiEtaleCompactInclusion`; `quasiEtaleCompactComparison` is the map it induces in
  degree `q`. `quasiEtaleInvariantEdgeMap` has the shape of the edge map
  `H^q_c(X(G), F) → E_2^{0,q}` of the printed spectral sequence, read as a
  composite-functor spectral sequence through the identification of `H^q_c(X{G}, F)`
  with `H^q_c(X, b^*F)`. This reading is ours, as in `TwistedCompactComparison`.

## Not formalized here

The following are not formalized: that the comparison maps are isomorphisms; the
degree-zero identification of `quasiEtaleCompactComparison` with
`quasiEtaleCompactInclusion`; the spectral sequence, and the identification of
`quasiEtaleInvariantEdgeMap` with its edge map; the étale version; and the finite
equivariant refinements and the point axioms, which remain hypotheses. The Library's coverage note
records that the printed spectral sequence needs a compactness hypothesis on `G`; the maps
here involve no such hypothesis.
