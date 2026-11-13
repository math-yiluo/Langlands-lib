# Equivariant and plain compactly supported cohomology on the étale site

Author: Worker 26. Uses Worker 26's modules
`Langlands.Sheaf.Equivariant.TwistedExactCompactComparison` (the comparison maps for an
exact abelian subcategory of sheaves on a twisted site, submitted together with this
module), `Langlands.Sheaf.Equivariant.AnalyticEtaleCompactCohomology` (essential
smallness of the étale and twisted étale sites, sheafification, enough injectives on the
twisted site, the abelian structure and enough injectives of étale `G`-sheaves,
`H^q_c(X{G}, F)` and `RΓ_c(X{G}, F)`, and the additivity of
`LocalActionSystem.smoothSheafInclusion`),
`Langlands.Sheaf.Equivariant.AnalyticCompactSupport` (the topology `pointTopology L X` on
`L`-valued points, `continuousConstSMul_pointAction`, the points `etalePoints L h`, the
local smallness `etaleSite_locallySmall_points` and `Γ_{c,X{G}}` on étale `G`-sheaves),
`Langlands.Sheaf.Equivariant.AnalyticGSheaves` (the twisted étale site, the lift system
`distinguishedLiftSystem ρ` and `EtaleGSheaf`) and
`Langlands.Sheaf.Equivariant.LocalActionSmoothPart` (exactness of the inclusion of
locally discrete sheaves). It also uses `Langlands.Sheaf.PointSupport`
(`sheafCompactSections`, `compactDerived`) and
`Langlands.Cohomology.DiscreteSheafDerivedComplex` (`sheafCompactComplex`). From Worker 21
it uses the étale site `EtaleSite`, its topology `etaleTopology`, the point axioms
`EtaleSite.PointAxioms`, the action `EtaleSite.pointAction` of `G` on `L`-valued points
and `EtaleSite.pointEquivariance`.

## Purpose

`AnalyticEtaleCompactCohomology` defines `H^q_c(X{G}, F)` for Berkovich's étale
`G`-sheaves on a `K`-analytic space `X`. Berkovich compares it with the compactly
supported cohomology of the underlying sheaf on `X` (Corollary 1.5.2(i)). This module
defines the other objects of that statement on the étale site, and the maps between
them. They are the constructions of `TwistedExactCompactComparison` with
`incl = (distinguishedLiftSystem ρ).smoothSheafInclusion`, the inclusion of étale
`G`-sheaves into sheaves on the twisted étale site. The module mirrors the published
quasi-étale module `AnalyticQuasiEtaleComparison` and defines:

- `Γ_c(X, -)`, `H^q_c(X, -)` and `RΓ_c(X, -)` for module sheaves on the étale site of `X`;
- Berkovich's `b^*`, the restriction from étale `G`-sheaves to sheaves on the étale site
  of `X`;
- `Γ_{c,X(G)}` and `H^q_c(X(G), F)` on étale `G`-sheaves, with the edge map
  `H^q_c(X(G), F) → H^q_c(X{G}, F)^G`;
- the comparison maps `H^q_c(X{G}, F) → H^q_c(X, b^*F)`, in each degree and as one map of
  complexes, and their compatibility on cohomology.

That the comparison maps are isomorphisms is not proved. They are not isomorphisms in
general; see "Supports in `L`-valued points" below.

All declarations are in `Langlands.Sheaf.Equivariant.Analytic`.

## Data and universes

As in `AnalyticEtaleCompactCohomology`:

- `K : Type u` is a complete ultrametric normed field and `X` an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`.
- `L : Type uL` is a normed field with `[NormedAlgebra K L]`, and
  `h : ∀ x, EtaleSite.PointAxioms L x` is the hypothesis that every `L`-valued point of
  `X` satisfies Worker 21's point axioms.
- `G : Type z` is a group with `ρ : G →* Aut X` and `[TopologicalSpace G]`; from the
  section on comparison on, `[IsTopologicalGroup G]`.
- `R : Type w` is a commutative ring, `w = max u (v + 1) uL`, and sheaves take values in
  `ModuleCat.{w} R`. Smooth representations are `SmoothRep.{w, z, w} R G`.
- Statements that need the abelian structure of étale `G`-sheaves assume `[Small.{w} G]`
  and `[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]`,
  the hypotheses of `AnalyticEtaleCompactCohomology`. Worker 26's module
  `AnalyticEtaleRefinements` derives the second from three conditions on distinguished
  étale objects; this module does not import it.

Some declarations carry the explicit universe list `.{u, v, uL}`. The universe `uL`
occurs in their types only inside `max u (v + 1) uL`, where Lean does not infer it. For
the same reason the size, sheafification, injectivity and exactness facts are theorems,
not instances, and are supplied locally with `haveI`, as in
`AnalyticEtaleCompactCohomology`.

## Plain compactly supported cohomology on the étale site

No group appears here, except in the Kan extension theorem.

- `etale_enoughInjectives X R`: module sheaves on the étale site of `X` have enough
  injectives. The site is essentially small in `w` (`etaleSite_essentiallySmall_points`),
  so Mathlib's `Sheaf.isGrothendieckAbelian_of_essentiallySmall` shows that the sheaf
  category is a Grothendieck abelian category, and
  `IsGrothendieckAbelian.enoughInjectives` concludes. The limits over
  `StructuredArrow Y (equivSmallModel _).inverse.op` that the first lemma needs exist by
  `hasLimitsOfShape_of_essentiallySmall`. The proof is the one of
  `quasiEtale_enoughInjectives`.
- `etaleSelf X`: `X` as an object of its étale site, by the identity. It is
  definitionally `(base etale ρ).obj` for every `ρ`.
- `etale_hasPointwiseRightKanExtension ρ R F` (with `[Small.{w} G]`): every module
  presheaf `F` on the étale site has a pointwise right Kan extension along the inclusion
  `(ι etale ρ).op` into the twisted étale site. The indexing categories
  `StructuredArrow Y (ι etale ρ).op` are essentially small in `w`, because the étale site
  is essentially small and the twisted étale site is locally small
  (`twistedEtale_locallySmall_points`), and `ModuleCat.{w} R` has limits of that size.
  The proof is the one of the published `quasiEtale_hasPointwiseRightKanExtension`.
- `etaleCompactSections L h R`: `Γ_c(X, F)`, the compactly supported global sections of a
  module sheaf `F`, with supports in the `L`-valued points. It is the published
  `sheafCompactSections` for the points `etalePoints L h` at `etaleSelf X`. It is additive
  (`etaleCompactSections_additive`).
- `etaleCompactCohomology L h R q`: `H^q_c(X, F)`, the published `compactDerived`, the
  right derived functors of `Γ_c(X, -)` computed with injective resolutions of module
  sheaves. `etaleCompactCohomologyZeroIso` identifies `H^0_c(X, -)` with `Γ_c(X, -)`.
- `etaleCompactComplex L h R`, with `[HasDerivedCategory.{w₄} (ModuleCat R)]`: the complex
  `RΓ_c(X, F)` in `DerivedCategory.Plus (ModuleCat R)`, the published
  `sheafCompactComplex`. The derived category of module sheaves it uses inside is
  Mathlib's `HasDerivedCategory.standard`, so no hypothesis about it is needed.
  `etaleCompactComplexHomologyIso F q` identifies its cohomology in degree `q` with
  `H^q_c(X, F)`, and `isZero_etaleCompactComplex_homology` gives vanishing in negative
  degrees.

## The restriction `b^*`

- `etaleGSheafRestriction ρ R`: from `EtaleGSheaf ρ (ModuleCat R)` to module sheaves on
  the étale site of `X`. It is `exactRestriction` of `TwistedExactCompactComparison` for
  the inclusion of étale `G`-sheaves: the inclusion into sheaves on the twisted étale
  site, followed by restriction along the inclusion of the étale site of `X`, which
  forgets the action of `G`. Its definition needs no refinement hypothesis.
- `etaleGSheafRestriction_additive`: it is additive (instance).
- `etaleGSheafRestriction_preservesFiniteLimits` and
  `etaleGSheafRestriction_preservesFiniteColimits` (with `[Small.{w} G]` and the
  refinement hypothesis): it is exact. These are `exactRestriction_preservesFiniteLimits`
  and `exactRestriction_preservesFiniteColimits`; the inclusion of étale `G`-sheaves is
  exact by `LocalActionSmoothPart`, and the right exactness of restriction rests on
  `etale_hasPointwiseRightKanExtension`.

## Invariant cohomology and the comparison maps

In this section `G` is a topological group. The topology on `L`-valued points, Worker
21's action `EtaleSite.pointAction L ρ` with `continuousConstSMul_pointAction`, local
smallness, sheafification on both sites, enough injectives for étale `G`-sheaves and for
module sheaves on the étale site, and the right Kan extensions are supplied locally. The
`TwistedOver.PointEquivariance` used throughout is Worker 21's
`EtaleSite.pointEquivariance L ρ h`.

- `etaleCompactInclusion L ρ h R`: the inclusion `Γ_{c,X{G}}(F) → Γ_c(X, b^*F)`, a
  natural transformation from `etaleGSheafCompactSections L ρ h R ⋙ smoothForget R G` to
  `etaleGSheafRestriction ρ R ⋙ etaleCompactSections L h R`. It is
  `exactCompactInclusion`, which sends a smooth compactly supported section to itself.
- `etaleGSheafInvariantCompactSections L ρ h R`: `Γ_{c,X(G)}`, defined as
  `etaleGSheafCompactSections L ρ h R` followed by `smoothInvariantsFunctor R G`, the
  `G`-invariant vectors. It is additive (instance).

From here on `[Small.{w} G]` and the refinement hypothesis are assumed.

- `etaleGSheafInvariantCompactCohomology L ρ h R q`: `H^q_c(X(G), F)`, the right derived
  functors of `Γ_{c,X(G)}` computed with injective resolutions among étale `G`-sheaves.
  `etaleGSheafInvariantCompactCohomologyZeroIso` identifies degree zero with
  `Γ_{c,X(G)}` (`exactInvariantCompactDerivedZeroIso`).
- `etaleInvariantEdgeMap L ρ h R q`: the natural transformation
  `H^q_c(X(G), F) → H^q_c(X{G}, F)^G`, to `etaleGSheafCompactCohomology L ρ h R q`
  followed by `smoothInvariantsFunctor R G`. It is `exactInvariantEdgeMap`, the
  comparison `LeftExactHomology.derivedNatTrans` for `Γ_{c,X{G}}` followed by the
  invariants. `isIso_etaleInvariantEdgeMap_zero`: it is an isomorphism in degree zero.
- `etaleCompactComparison L ρ h R q`: the comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)`
  in degree `q`, a natural transformation from
  `etaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G` to
  `etaleGSheafRestriction ρ R ⋙ etaleCompactCohomology L h R q`. It is
  `exactCompactComparison`, the base change of `etaleCompactInclusion` along the exact
  functors `b^*` and `smoothForget`.

With `[HasDerivedCategory.{w₃} (SmoothRep R G)]` and
`[HasDerivedCategory.{w₄} (ModuleCat R)]`; the derived categories of étale `G`-sheaves
and of module sheaves used inside are Mathlib's standard ones, as for `RΓ_c(X{G}, F)` in
`AnalyticEtaleCompactCohomology`:

- `etaleCompactComplexComparison L ρ h R`: the comparison
  `RΓ_c(X{G}, F) → RΓ_c(X, b^*F)` in `DerivedCategory (ModuleCat R)`, a natural
  transformation from `etaleGSheafCompactComplex L ρ h R`, followed by
  `DerivedCategory.Plus.ι` and the derived functor of the exact functor
  `smoothForget R G`, to `etaleGSheafRestriction ρ R ⋙ etaleCompactComplex L h R`
  followed by `DerivedCategory.Plus.ι`. It is `exactCompactComplexComparison`.
- `etaleCompactComplexForgetHomologyIso L ρ h R F q`: the cohomology in degree `q` of the
  image of `RΓ_c(X{G}, F)` under the derived `smoothForget` is the module underlying
  `H^q_c(X{G}, F)` (`exactCompactComplexForgetHomologyIso`).
- `etaleCompactComplexComparison_homology L ρ h R F q`: on cohomology in degree `q`, the
  comparison of complexes, followed by `etaleCompactComplexHomologyIso` for `b^*F`,
  equals `etaleCompactComplexForgetHomologyIso` followed by `etaleCompactComparison` in
  degree `q` (`exactCompactComplexComparison_homology`).

All these definitions typecheck against the published `etaleGSheafCompactCohomology`
and `etaleGSheafCompactComplex` by unfolding: `etaleGSheafCompactSections` is
definitionally `exactCompactSections` for the inclusion of étale `G`-sheaves.

## Supports in `L`-valued points

The following is a mathematical remark. It is not formalized.

Supports are taken in the `L`-valued points. When some point of `|X|` is not the image of
an `L`-valued point, the degree-zero inclusion `etaleCompactInclusion` need not be
surjective, so (through the identification of `H^0` with sections, not formalized here)
the degree-zero comparison map is not an isomorphism. Worker 16's example for the
quasi-étale model, in the coverage note `notes/henniart/harris-cohomology-coverage.md`
(section "Retained source gaps and scope decisions"), adapts as follows. Take
`K = ℚ_p` and `L = ℂ_p`, and assume the point axioms `h` for `L`. Let `G = ℤ_p` act on
`X = ⊔_{n ≥ 0} ⊔_{i ∈ ℤ/p^{n+1}} D_{n,i}`, a disjoint union of copies of the closed unit
disc, by permuting the copies of the `n`-th block through `ℤ_p → ℤ/p^{n+1}`. Let
`ζ_{n,i}` be the Gauss point of `D_{n,i}`, and `F` the étale sheaf whose sections over an
étale `U → X` are the functions, with values in a nonzero module `M`, on the points of
`U` lying over the `ζ_{n,i}`, with `G` permuting the copies.

- `F` is an étale `G`-sheaf in the sense of Definition 1.4.1. For a quasi-étale `U → X`
  with compact `U`, the points of `U` over the `ζ_{n,i}` form a finite set `S`, and
  `F(U)` is the module of `M`-valued functions on `S`. The canonical continuous action
  of `G_U` on `U` (printed p.7) permutes `S`. Each point of `S` has a neighbourhood
  containing no other point of `S`, so by continuity its stabilizer in `G_U` is open.
  The pointwise stabilizer of `S` is therefore open, and it acts trivially on `F(U)`.
- Let `f ∈ F(X)` be `m ≠ 0` at `ζ_{n,0}` for every `n` and `0` elsewhere. Its stabilizer
  in `G` is `⋂_n p^{n+1} ℤ_p = 0`, which is not open, so `f` is not in `Γ_{c,X{G}}(F)`.
- No `ℂ_p`-valued point lies over a Gauss point: the residue field `𝔽_p(T)` of the
  completed residue field of `ζ_{n,i}` does not embed in the residue field `𝔽̄_p` of
  `ℂ_p`. Every `ℂ_p`-valued point therefore lies over a point `y ≠ ζ_{n,i}` of some
  `D_{n,i}`. Since `X` is Hausdorff, `y` has an open neighbourhood missing `ζ_{n,i}`, on
  which `F` vanishes. So every germ of `f` at a `ℂ_p`-valued point vanishes, the support
  of `f` is empty, and `f` lies in `Γ_c(X, b^*F)`.

This does not contradict Berkovich's Corollary 1.5.2(i). There the support of `f` is
taken in all points of `X`; it is `{ζ_{n,0} : n ≥ 0}`, an infinite closed discrete set,
so `f` is not compactly supported. Whether the comparison maps are isomorphisms when
every point of `|X|` is the image of an `L`-valued point has not been checked.

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
- §1.4, printed p.7 = PDF p.7, cited in the remark above: "It follows that for any
  quasi-étale morphism U → X with compact U the action of G on X extends in a canonical
  way to a continuous action of some open subgroup G_U ⊂ G on U." Definition 1.4.1,
  printed pp.7–8: "A quasi-étale (resp. étale) G-sheaf on X is a quasi-étale (resp.
  étale) G^d-sheaf F such that for any quasi-étale morphism U → X with compact U the
  action of G_U on F(U) is discrete."

## Provenance and correspondence

This module specializes derived infrastructure. The correspondence with Berkovich is the
one recorded in `TwistedCompactComparison` and `AnalyticEtaleCompactCohomology`. The
choices below are ours:

- Berkovich's statement is for étale abelian sheaves on `X(G)`. Here the source category
  is `EtaleGSheaf`, the twisted model of `T_G(X_ét)`, as for `H^q_c(X{G}, F)` in
  `AnalyticEtaleCompactCohomology`; by Berkovich's Theorem 1.4.2 (printed p.8) the two
  categories are equivalent, which is not formalized.
- `b^*` is restriction of the twisted model to the étale site of `X`. Sections over
  `X(G)` are the `G`-invariant sections of the underlying sheaf (proof of Theorem 1.4.2,
  printed p.9), so `Γ_{c,X(G)}` is modelled by the `G`-invariant vectors of
  `Γ_{c,X{G}}`.
- Berkovich takes the derived functors of `Γ_{c,X(G)}` on all étale abelian sheaves on
  `X(G)`. Here they are taken among étale `G`-sheaves, which needs the abelian structure
  of `LocalActionSmoothPart` under the refinement hypothesis.
- Supports are taken in the `L`-valued points with the topology induced from `|X|`, as in
  `AnalyticCompactSupport`, and the point axioms are a hypothesis. Berkovich takes them in
  all points of `X`; the remark above shows that the difference matters.
- In degree zero, the comparison map of Corollary 1.5.2(i) is the inclusion
  `etaleCompactInclusion`; `etaleCompactComparison` is the map it induces in degree `q`.
  `etaleInvariantEdgeMap` has the shape of the edge map `H^q_c(X(G), F) → E_2^{0,q}` of
  the printed spectral sequence, read as a composite-functor spectral sequence through
  the identification of `H^q_c(X{G}, F)` with `H^q_c(X, b^*F)`. This reading is ours, as
  in `TwistedCompactComparison`.

## Not formalized here

Conditions under which the comparison maps are isomorphisms (they are not in general,
see the remark above); the degree-zero identification of `etaleCompactComparison` with
`etaleCompactInclusion`; the spectral sequence, and the identification of
`etaleInvariantEdgeMap` with its edge map; Theorem 1.4.2; the comparison with the
quasi-étale constructions of `AnalyticQuasiEtaleComparison`; and the refinement
hypothesis and the point axioms, which remain hypotheses. The Library's coverage note
records that the printed spectral sequence needs a compactness hypothesis on `G`; the
maps here involve no such hypothesis.
