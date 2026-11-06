# Coefficients pulled back from a base along a level tower

This internal construction supplies the basic coefficients for the published
colimit cohomology of level towers, and their functoriality in the tower. Let
a tower of schemes on compact open levels lie over a base scheme `X`. Each
module sheaf `M` on `X` is pulled back to every level by the actual inverse
image along the projection. The resulting coefficients are compatible, and
they are level-trivial whenever each `k ∈ K` acts on level `K` by the
identity. The construction therefore gives smooth representations on the
colimit cohomology and colimit global sections with these coefficients,
natural in `M`. A morphism of towers over `X` with étale components induces
pullback maps of these representations, with identity and composition laws.
Consequently, a group acting on the tower by automorphisms over `X` acts on
these representations, commuting with the action of `G`.
The module also adds the generic sections functor and degree-zero
identification for arbitrary level-trivial coefficient diagrams. All
declarations are in namespace `Langlands.Shimura.LevelTowerCohomology`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, studies the cohomology of towers of Shimura varieties with the action
of the finite adelic group. Examples are the prime-to-ℓ finite adeles after
(3.5) on printed p. 307, and `GG(A_f^{ℓ,p})` as `K(N)^{ℓ,p}` varies in
Proposition 4.10 on printed p. 311. The simplest coefficients come from the
base, such as constant coefficients on the Shimura varieties over their field
of definition. This module treats exactly such coefficients for an arbitrary
tower satisfying the stated hypotheses. Morphisms of towers, such as
automorphisms over the base, act on the resulting cohomology. Harris's
passages are only motivation. The module constructs no Shimura varieties and
none of Harris's automorphic coefficient systems, which are in general not
pulled back from the base. It constructs no particular Galois action, no
Hecke-algebra action, no finiteness, no compact support and no comparison
with a limit scheme.

## Projection comparisons on arbitrary schemes

Let `R : Type u` be a commutative ring and let `X`, `Y`, `Z` be schemes. Let
`f : Y ⟶ Z` be étale, and let `q : Z ⟶ X` and `r : Y ⟶ X` be arbitrary with
`h : f ≫ q = r`.

- `restrictionProjectionIso R q r f h` is a natural isomorphism from
  `inverseImage q R ⋙ restriction f` to `inverseImage r R`. It is the inverse
  of the published comparison `inverseImageIsoRestriction f R`, whiskered by
  `inverseImage q R`, followed by the published triangle comparison
  `projectionInverseImageIso R q r f h`
  (`restrictionProjectionIso_hom_app`).
- `restrictionProjectionIso_congr` states the following. For equal étale maps
  `f = g`, the comparison for `f` is the published `restrictionCongr` along
  `f = g`, followed by the comparison for `g`.
- `restrictionProjectionIso_id` states that, for `f = 𝟙 Y`, the comparison is
  the published identity constraint `restrictionId`. The proof uses the
  published `projectionInverseImageIso_id` and `inverseImageIsoRestriction_id`.
- `inverseImageIsoRestriction_comp_inv_app` is the inverse form of the
  published `inverseImageIsoRestriction_comp`, evaluated at a sheaf.
- `restrictionProjectionIso_comp` concerns étale maps `f : Y₁ ⟶ Y₀` and
  `g : Y₂ ⟶ Y₁` with triangles `f ≫ q₀ = q₁`, `g ≫ q₁ = q₂` and
  `(g ≫ f) ≫ q₀ = q₂`. Restricting the comparison for `f` along `g`, then
  applying the comparison for `g`, gives the comparison for `g ≫ f`. The
  published inverse composition constraint `restrictionComp f g` is applied
  first. The proof combines the published `projectionInverseImageIso_comp`
  with the previous lemma.
- `projectionCohomologyMap R q r f h n M` is the published
  `cohomologyMapWithCoefficients f R n` with coefficient map the comparison
  at `M`. It maps `H^n(Z, q^* M)` to `H^n(Y, r^* M)`. It depends only on `f`
  (`projectionCohomologyMap_congr`) and is the identity for `f = 𝟙 Y`
  (`projectionCohomologyMap_id`). Successive pullbacks compose to the pullback
  along the composite (`projectionCohomologyMap_comp`). It is natural in `M`
  (`projectionCohomologyMap_naturality`).

## Inputs on towers

Let `G : Type u` be a group with a topology. Let
`T : CompactOpenLevel G ⥤ Scheme.{u}` be a functor on the published
transporter category of compact open levels, with `Etale (T.map a)` for every
level arrow `a`. Let `X : Scheme.{u}` be a scheme. The projections are a
natural transformation `p : T ⟶ (Functor.const (CompactOpenLevel G)).obj X`.
Its components are scheme maps `p_K : T K ⟶ X` with `T.map a ≫ p_L = p_K`
for `a : K ⟶ L`. The projections need not be étale.

- `baseCone p` is the same data as a natural transformation from the
  constant diagram at `op X` to `T.op`. Its component at `K` is
  `(p.app K.unop).op`, and naturality is the opposite of the naturality of
  `p`. `baseCone_app_unop` records the component.
- The instances `etale_id_app` and `etale_comp_app` state that identity
  morphisms of towers have étale components, and that composites of tower
  morphisms with étale components have étale components.

## Generic additions for level-trivial coefficients

Assume that `G` is a topological group. For the published
`levelTrivialCoefficients T R` property of restriction coefficient diagrams
on `T.op`:

- `smoothColimitSectionsFunctor T R` is the functor to smooth
  representations given by the colimit over levels of global sections. It
  lifts the published `CoefficientDiagram.sectionsFunctor` into level-trivial
  presheaves, using the published `isLevelTrivial_sections`, and composes with
  the published `LevelColimit.smoothFunctor`. On objects it is the published
  `smoothColimitSections` (`smoothColimitSectionsFunctor_obj`).
- `smoothColimitCohomologyZeroIso T R` is a natural isomorphism from the
  published degree-zero `smoothColimitCohomologyFunctor T R 0` to this
  sections functor. It applies `LevelColimit.smoothFunctor` to the published
  degree-zero identification `CoefficientDiagram.cohomologyZeroFunctorIso`.

## Pulled-back coefficients

Let `M` be a module sheaf on the small étale site of `X`.

- `canonicalCoefficients R p M` is a restriction coefficient diagram on
  `T.op`. It is the published geometric diagram
  `EtaleGeometricDiagram.canonicalCoefficients R (baseCone p) M`, transported
  by the published `CoefficientDiagram.toRestriction` along the étale level
  maps. Its sheaf at `op K` is the actual inverse image `p_K^* M`
  (`canonicalCoefficients_obj`).
- `canonicalCoefficients_map` states that the transition along
  `a : K ⟶ L` in `(CompactOpenLevel G)ᵒᵖ` is
  `restrictionProjectionIso R p_K p_L (T.map a.unop) _` at `M`. The
  triangle is the published `baseProjection_triangle`.
  `canonicalCoefficients_cohomology_map` states that the cohomology
  transition is the corresponding `projectionCohomologyMap`.
- `canonicalCoefficients_map_congr` states the following. If two level arrows
  `a b : K ⟶ L` give the same scheme morphism, their coefficient transitions
  differ exactly by `restrictionCongr` along that equality.
- `canonicalCoefficientsFunctor R p` is the composite of the published
  `EtaleGeometricDiagram.canonicalCoefficientsFunctor` and
  `toRestrictionFunctor`. It sends a morphism `α : M ⟶ N` to the inverse
  images `p_K^*(α)` at every level (`canonicalCoefficientsFunctor_obj`,
  `canonicalCoefficientsFunctor_map_app`).
- `canonicalCoefficients_cohomology_obj` records that the degree `q`
  cohomology at level `K` is the published étale cohomology of `T K` with
  coefficients `p_K^* M`.

## Level triviality and smooth representations

The hypothesis `hT` states that `T.map (selfArrow K k hk) = 𝟙 (T K)` for
every level `K` and every `k ∈ K`. It is a condition on the given geometry.

- `isLevelTrivialCoefficients_canonical R hT M` proves that the pulled-back
  coefficients satisfy the published `IsLevelTrivialCoefficients`. By `hT`
  and the identity law of `T`, the self-arrow and the identity arrow give the
  same scheme morphism. `canonicalCoefficients_map_congr` then supplies the
  required coefficient equation. No coefficient condition is assumed.
- `levelTrivialCanonicalCoefficientsFunctor R p hT` lifts
  `canonicalCoefficientsFunctor R p` into the full subcategory of
  level-trivial coefficient diagrams.

Assume that `G` is a topological group.

- `smoothCanonicalCohomologyFunctor R p hT q` is the composite with the
  published `smoothColimitCohomologyFunctor T R q`. It sends `M` to the colimit
  over shrinking levels of `H^q(T K, p_K^* M)`, as a smooth representation of
  `G` (`smoothCanonicalCohomologyFunctor_obj`). It is a functor in the base
  sheaf `M`.
- `smoothCanonicalSectionsFunctor R p hT` is the analogous functor for global
  sections (`smoothCanonicalSectionsFunctor_obj`).
- `smoothCanonicalCohomologyZeroIso R p hT` identifies degree zero with
  sections, by whiskering `smoothColimitCohomologyZeroIso T R`.
- `smoothCanonicalCohomology_ρ_ι_apply` specializes the published action
  formula. Let `g ∈ G` and let `x` be a class of level `K`. Then `g` sends the
  image of `x` to the image at level `g K g⁻¹` of the pullback of `x` along
  `T.map (conjArrow g K)`, followed by the coefficient transition of that
  arrow.
- `canonicalCohomology_exists_level` states that, when some compact open
  level exists, every class of the colimit comes from
  `H^q(T K, p_K^* M)` for a single level `K`.

Constant coefficients are the special case where `M` is a constant sheaf on
`X`. This module does not identify `p_K^* M` with the constant sheaf on
`T K`. The published `EtaleInverseImageConstant` module gives such an
identification at each level, but it is not used here.

## Morphisms of towers

Let `T'` be a second tower with étale level maps, and let `φ : T' ⟶ T` be a
natural transformation whose components `φ_K : T' K ⟶ T K` are étale. Let
`p'` be projections of `T'` to `X` with `hφ : φ ≫ p = p'`, so that `T'` lies
over `X` through `T`.

- `canonicalPullback R p φ hφ M n` is a natural transformation from the
  degree `n` cohomology diagram of `canonicalCoefficients R p M` to that of
  `canonicalCoefficients R p' M`. At level `K` it is
  `projectionCohomologyMap R p_K p'_K φ_K _ n M` (`canonicalPullback_app`).
  Naturality in the level follows from `projectionCohomologyMap_comp`, applied
  to both composites. `projectionCohomologyMap_congr` along the naturality
  square of `φ` then identifies them.
- `canonicalPullbackNatTrans R p φ hφ n` is the same family, natural in the
  base sheaf `M`, by `projectionCohomologyMap_naturality`.
- `canonicalPullback_id` states that pullback along `𝟙 T` is the identity.
  For `ψ : T'' ⟶ T'` with étale components and `ψ ≫ p' = p''`,
  `canonicalPullback_comp` states that pullback along `φ` followed by
  pullback along `ψ` is pullback along `ψ ≫ φ`.
- `canonicalPullback_ι` states, on colimits over levels, that the published
  `LevelColimit.map` of the pullback sends the image of a class of level `K`
  to the image of its pullback along `φ_K`.

Assume moreover that `G` is a topological group and that `T`, `T'` and `T''`
satisfy the level-triviality hypotheses `hT`, `hT'` and `hT''`.

- `smoothCanonicalPullback R p φ hφ hT hT' n` is a natural transformation from
  `smoothCanonicalCohomologyFunctor R p hT n` to
  `smoothCanonicalCohomologyFunctor R p' hT' n`. Its component at `M` is the
  published `LevelColimit.smoothFunctor` applied to `canonicalPullback`
  (`smoothCanonicalPullback_app`). Each component is thus a morphism of smooth
  representations, so it commutes with the action of `G`.
- `smoothCanonicalPullback_id` and `smoothCanonicalPullback_comp` are the
  identity and composition laws at this level.

## Automorphism actions

The instance `etale_iso_hom_app` states that the components of an
isomorphism of towers are étale. Keep the hypotheses `hT` and the
topological group `G`.

- `smoothCanonicalPullback_of_eq_id` and
  `smoothCanonicalPullback_of_eq_comp` restate the identity and composition
  laws for endomorphisms of `T` over `X`. They apply to an endomorphism equal
  to `𝟙 T`, and to an endomorphism `χ = ψ ≫ φ`, for which the smooth pullback
  along `χ` is that along `φ` followed by that along `ψ`.
- Let `Γ : Type v` be a group and `ρ : Γ →* (Aut T)ᵐᵒᵖ` a homomorphism.
  Following the convention of the published deck actions, `γ` gives the
  automorphism `(ρ γ).unop` of the tower. The automorphisms are assumed to
  lie over the base, `hρ γ : (ρ γ).unop.hom ≫ p = p`.
- `automorphismAction R p hT ρ hρ n M` is an object of
  `Action (SmoothRep R G) Γ`. Its underlying smooth representation is
  `(smoothCanonicalCohomologyFunctor R p hT n).obj M`, and `γ` acts by the
  smooth pullback along `(ρ γ).unop.hom` (`automorphismAction_ρ`). The unit
  and multiplication laws follow from the two previous lemmas, using
  `ρ (γ * δ) = ρ γ * ρ δ` and the published multiplication `f * g = g ≪≫ f`
  of `Aut`. Since every `γ` acts by a morphism of smooth representations,
  the action of `Γ` commutes with that of `G`.
- `automorphismActionFunctor R p hT ρ hρ n` makes this a functor of the base
  sheaf, by naturality of the smooth pullbacks.
  `automorphismActionForgetIso` identifies its composite with the forgetful
  functor `Action.forget` with `smoothCanonicalCohomologyFunctor R p hT n`.

No topology on `Γ` and no continuity of its action is considered.

## Provenance

This is an internal assembly of published results:

- `EtaleGeometricDiagram.canonicalCoefficients` and its functor;
- the published equivalence `toRestriction` between geometric and
  restriction coefficient diagrams along étale maps;
- the published inverse-image comparisons `inverseImageIsoRestriction`,
  `inverseImageComp`, `inverseImageCongr`, `projectionInverseImageIso` and
  `restrictionCongr`, with their identity and composition laws;
- the published cohomology pullbacks `cohomologyMapWithCoefficients`,
  `cohomologyMap_id` and `cohomologyMapWithCoefficients_comp`;
- the published `LevelTowerCohomology` colimit cohomology, smoothness,
  action formula and representative results;
- the published `LevelColimit.map`, `LevelColimit.ι_map` and
  `LevelColimit.smoothFunctor`;
- Mathlib's groups `Aut` and monoids `End` of a category, and its category
  `Action` of objects with a monoid action.

No cohomology groups, actions, smoothness, coefficient compatibilities or
functoriality laws are supplied as input. Harris's passages are cited only as
motivation, and no statement from them is formalized.
