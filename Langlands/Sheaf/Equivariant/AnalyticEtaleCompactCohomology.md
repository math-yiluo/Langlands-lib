# Compactly supported cohomology of étale `G`-sheaves on analytic spaces

Author: Worker 26. Uses the published `Langlands.Sheaf.Equivariant.AnalyticCompactSupport`
(topology on `L`-valued points and `Γ_{c,X{G}}` on étale `G`-sheaves, Worker 26),
`Langlands.Sheaf.Equivariant.AnalyticGSheaves` (twisted étale site, lifts on
distinguished étale objects, étale `G`-sheaves, Worker 26),
`Langlands.Sheaf.Equivariant.TwistedCompactSupport` (compactly supported sections on a
twisted site, Worker 26) and `Langlands.Cohomology.DerivedPlus` (derived complexes in the
bounded below derived category). It also uses the module
`Langlands.Sheaf.Equivariant.LocalActionSmoothPart` (Worker 26; abelian structure and
enough injectives of locally discrete sheaves). From Worker 21 it uses the étale site `EtaleSite` and its points given by
`L`-valued points (`EtaleSite.PointAxioms`, `EtaleSite.toPoint`,
`EtaleSite.pointEquivariance`).

## Purpose

Let a group `G` act on a `K`-analytic space `X`. The published module
`AnalyticCompactSupport` defines Berkovich's compactly supported sections
`Γ_{c,X{G}}` on étale `G`-sheaves (`etaleGSheafCompactSections`). It does not define
their derived functors, because the étale `G`-sheaves (`EtaleGSheaf`, the locally
discrete sheaves of the lift system on distinguished étale objects) were not known to
form an abelian category with enough injectives. `LocalActionSmoothPart` proves both
for any local action system under the hypothesis `HasAdmissibleRefinements`. This
module specializes it to the twisted étale site. It

- proves that the étale site and the twisted étale site are essentially small in the
  universe of the coefficients, and deduces that module sheaves on them have
  sheafification and that module sheaves on the twisted étale site have enough
  injectives;
- under `HasAdmissibleRefinements` for `distinguishedLiftSystem ρ`, gives the abelian
  structure and enough injectives on étale `G`-sheaves of modules;
- defines `H^q_c(X{G}, F)` for étale `G`-sheaves of modules as the right derived
  functors of `Γ_{c,X{G}}`, and the complex `RΓ_c(X{G}, F)`.

It also adds one general instance, `LocalActionSystem.smoothSheafInclusion_additive`:
for any local action system `L` on a site `(T, J)` and any commutative ring `R`, the
inclusion `L.smoothSheafInclusion (ModuleCat R) J` of locally discrete module sheaves
is additive. The inclusion is a `def` in `LocalAction`, so Mathlib's instance for the
inclusion `ι` of a full subcategory does not apply to it directly; the proof is that
instance. This instance lies in `Langlands.Sheaf.Equivariant.LocalActionSystem`; all
other declarations are in `Langlands.Sheaf.Equivariant.Analytic`.

## Data and universes

- `K : Type u` is a complete ultrametric normed field and `X` an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`.
- `L : Type uL` is a normed field with `[NormedAlgebra K L]`. Write
  `P = localizedFieldPointFunctor L`.
- `G : Type z` is a group with `[TopologicalSpace G]` and `ρ : G →* Aut X`. The
  smooth representations and the cohomology also use `[IsTopologicalGroup G]`.
- Coefficients: `R : Type (max u (v + 1) uL)` is a commutative ring and sheaves take
  values in `ModuleCat.{max u (v + 1) uL} R`. As in `AnalyticCompactSupport`, this is
  the universe of Worker 21's points `EtaleSite.toPoint L x (h x)`. Write
  `w = max u (v + 1) uL`.
- `[Small.{w} G]` is assumed for the statements about the twisted site. It holds,
  for example, when `G` lies in a universe at most `w`.
- `h : ∀ x : P.obj X, EtaleSite.PointAxioms L x`: every `L`-valued point satisfies
  Worker 21's point axioms. This is a hypothesis, as in `AnalyticCompactSupport`.

## Size, sheafification and injectives

These are theorems rather than instances. Their universe `uL` occurs only inside
`max u (v + 1) uL`, and Lean's instance search does not solve the resulting universe
constraints. The definitions below supply them locally with `haveI`. The proofs follow
the quasi-étale ones in `AnalyticQuasiEtaleCompactCohomology`.

- `etaleSite_essentiallySmall_points X`: `EtaleSite X` is essentially small in
  universe `w`. It is locally small in `w` by the published
  `etaleSite_locallySmall_points`; its objects lie in `Type (max u (v + 1))`, so
  Mathlib's `small_lift` applies, and `essentiallySmall_of_small_of_locallySmall`
  concludes.
- `twistedEtale_locallySmall_points X ρ` (with `[Small.{w} G]`): the morphisms of
  the twisted étale site are small in `w`. A twisted morphism `U ⟶ V` is determined by
  its twist in `G` and its underlying arrow (`TwistedOver.Hom.ext`), so it injects into
  `G × (U.obj.left ⟶ V.obj.left)`.
- `twistedEtale_essentiallySmall_points X ρ`: the twisted étale site is essentially
  small in `w`.
- `etale_hasSheafify X R` and `twistedEtale_hasSheafify X ρ R`: module sheaves on both
  sites have sheafification, by Mathlib's `hasSheafifyEssentiallySmallSite`.
- `twistedEtale_enoughInjectives X ρ R`: `Sheaf (twistedEtaleTopology ρ)
  (ModuleCat R)` has enough injectives. Mathlib's
  `Sheaf.isGrothendieckAbelian_of_essentiallySmall` shows that it is a Grothendieck
  abelian category, and `IsGrothendieckAbelian.enoughInjectives` concludes. The limits
  over the comma categories `StructuredArrow Y (equivSmallModel _).inverse.op` needed by
  the first lemma exist because these categories are essentially small in `w`
  (`hasLimitsOfShape_of_essentiallySmall`).

## Étale `G`-sheaves of modules

The hypothesis of the rest of the module is
`[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]`,
the class of `LocalActionSmoothPart`. Its two fields say:

- every arrow `p : V' ⟶ V` of the twisted étale site between objects with admissible
  local actions `a'` and `a` restricts discreteness from `a` to `a'`
  (`IsRestrictionEquivariant a a' p`): for every open subgroup `K` of the group acting
  on `V`, some open subgroup `M` of the group acting on `V'` satisfies: for each
  `h ∈ M` there is `k ∈ K` with `(a' h).unop ≫ p = p ≫ (a k).unop`;
- for every cospan `f₁ : V₁ ⟶ U`, `f₂ : V₂ ⟶ U` and every cone `k₁ : W ⟶ V₁`,
  `k₂ : W ⟶ V₂` over it, the arrows `e : W' ⟶ W` that factor as `k : W' ⟶ V`
  followed by `p₁ : V ⟶ V₁`, `p₂ : V ⟶ V₂` from an object `V` with an admissible
  local action, with `p₁ ≫ f₁ = p₂ ≫ f₂` and `k ≫ pᵢ = e ≫ kᵢ`, form a covering
  sieve of `W`.

Here the objects with admissible local actions are the twisted étale objects whose
structure morphism is distinguished étale, with the restrictions of lifts of the action
to open subgroups (`distinguishedLiftSystem ρ`). The intended reading is the
`N`-morphism statements derived from Berkovich's Key Lemma and the covering of fibre
products by distinguished étale objects (see the source section). The hypothesis is
not proved in this module; no instance is constructed.

- `etaleGSheafAbelian ρ R`: the abelian structure on
  `EtaleGSheaf ρ (ModuleCat R)`. It is the generic
  `LocalActionSystem.smoothSheaf_abelian` with sheafification from
  `twistedEtale_hasSheafify`. It is an `abbrev`, not an instance, for the universe
  reason above.
- `etaleGSheaf_enoughInjectives ρ R`: `EtaleGSheaf ρ (ModuleCat R)` has enough
  injectives. It is the generic `LocalActionSystem.smoothSheaf_enoughInjectives`,
  which transports injectives along the locally discrete part (a right adjoint of the
  exact inclusion), applied with `twistedEtale_enoughInjectives`.

## Compactly supported sections

- `etaleGSheafCompactSections_eq L ρ h R` (by `rfl`): the published
  `etaleGSheafCompactSections L ρ h R` is the inclusion
  `(distinguishedLiftSystem ρ).smoothSheafInclusion` followed by the published
  `etaleCompactSectionsSmooth L ρ h R`.
- `etaleGSheafCompactSections_additive`: it is additive (instance; no refinement
  hypothesis is needed).
- `etaleGSheafCompactSections_preservesFiniteLimits L ρ h R` (with the refinement
  hypothesis and `[Small.{w} G]`): it preserves finite limits, for the finite limits
  of `etaleGSheafAbelian`. The inclusion preserves finite limits by
  `LocalActionSmoothPart`, and the published `sheafCompactSectionsSmooth` preserves
  them. It is a theorem, not an instance, for the universe reason above.

## Cohomology with compact support

The hypotheses are `h`, `[Small.{w} G]` and the refinement hypothesis.

- `etaleGSheafCompactCohomology L ρ h R q`:
  `EtaleGSheaf ρ (ModuleCat R) ⥤ SmoothRep R G`, Berkovich's `H^q_c(X{G}, F)` for
  étale `G`-sheaves of modules. It is Mathlib's `Functor.rightDerived q` of
  `etaleGSheafCompactSections L ρ h R`, computed with injective resolutions in the
  category of étale `G`-sheaves (abelian structure `etaleGSheafAbelian`, injective
  resolutions from `etaleGSheaf_enoughInjectives`).
- `etaleGSheafCompactCohomologyZeroIso`: `H^0_c(X{G}, -) ≅ Γ_{c,X{G}}` (Mathlib's
  `rightDerivedZeroIsoSelf`, using left exactness).
- `etaleGSheafCompactCohomologyIso I q`: for an injective resolution `I` of `F` among
  étale `G`-sheaves, `H^q_c(X{G}, F)` is the `q`-th cohomology of `Γ_{c,X{G}}` applied
  to `I`.
- `isZero_etaleGSheafCompactCohomology_succ_of_injective F q`:
  `H^{q+1}_c(X{G}, F) = 0` for injective `F`.
- `etaleGSheafCompactComplex L ρ h R`, with
  `[HasDerivedCategory.{w'} (SmoothRep R G)]`: the complex `RΓ_c(X{G}, F)` in
  `DerivedCategory.Plus (SmoothRep R G)`. It is the published
  `DerivedPlus.derivedComplex` of `Γ_{c,X{G}}`. That construction needs a derived
  category of the source; here it is Mathlib's `HasDerivedCategory.standard` for étale
  `G`-sheaves, so no hypothesis about it is needed.
- `etaleGSheafCompactComplexHomologyIso F q`: the cohomology of `RΓ_c(X{G}, F)` in
  degree `q` is `H^q_c(X{G}, F)`.
- `isZero_etaleGSheafCompactComplex_homology F hn`: `RΓ_c(X{G}, F)` has no cohomology
  in negative degrees.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (folder
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).

- §1.5, printed p.11 = PDF p.11, before Corollary 1.5.2: "Let F be an étale abelian
  sheaf on X(G). The support of an element f ∈ F(X(G)) is the set
  Supp(f) = {x ∈ X | f_x ≠ 0} … The values of the high direct images of the functor
  F ↦ Γ_{c,X{G}}(F) := lim_→ Γ_{c,X(N)}(F), where N runs through open subgroups of G,
  are denoted by H^q_c(X{G}, F)."
- §1.4, printed p.8, the remark after Definition 1.4.1: "It is easy to see that an
  étale `G^d`-sheaf `F` is a `G`-sheaf if and only if for any étale morphism
  `U → X` and any element `f ∈ F(U)` each point of `U` has a distinguished open
  neighborhood `𝒰` such that the stabilizer of `f|_𝒰` is open in `G_𝒰`." This is the
  criterion modelled by `EtaleGSheaf` (see `AnalyticGSheaves`).
- Theorem 1.4.2, printed p.8: "The inverse image functor for the morphism
  b : X → X(G) induces an equivalence of categories X(G)~_qét ⥲ T_G(X_qét)
  (resp. X(G)~_ét ⥲ T_G(X_ét))."
- §1.4, printed pp.7–8: the Key Lemma statements on `N`-morphisms that the first field
  of `HasAdmissibleRefinements` abstracts; they are quoted in
  `LocalActionSmoothPart.md`.

## Provenance and correspondence

This module specializes derived infrastructure. The choices below are ours:

- Berkovich defines `H^q_c(X{G}, F)` as derived functors on étale abelian sheaves on
  `X(G)`. Here they are derived functors on `EtaleGSheaf`, the twisted model of
  `T_G(X_ét)`. By Theorem 1.4.2 the two categories are equivalent, and derived
  functors are invariant under equivalence; Theorem 1.4.2 itself is not formalized.
- Coefficients are module sheaves over a commutative ring `R` in the universe `w`;
  abelian sheaves are the case of `ULift ℤ`.
- The abelian structure and enough injectives of `EtaleGSheaf` come from
  `LocalActionSmoothPart` under `HasAdmissibleRefinements`, not from Theorem 1.4.2.
  That hypothesis is not proved here.
- Supports are taken in the `L`-valued points with the topology induced from `|X|`,
  as in `AnalyticCompactSupport`. The same remarks on compactness and stalks apply
  there. The point axioms are a hypothesis.
- Essential smallness relies on the coefficient universe `max u (v + 1) uL`, which
  contains the objects of the sites.

## Not formalized here

A proof of `HasAdmissibleRefinements` for the distinguished lift system (from the Key
Lemma and the structure of distinguished étale morphisms), the point axioms for
complete algebraically closed `L`, Theorem 1.4.2, the comparison
`H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` of Corollary 1.5.2, and the comparison with the
quasi-étale cohomology of `AnalyticQuasiEtaleCompactCohomology`.
