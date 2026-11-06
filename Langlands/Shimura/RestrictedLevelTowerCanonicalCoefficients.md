# Coefficients pulled back from a base along a tower over levels satisfying a property

This internal construction repeats the published
`Langlands.Shimura.LevelTowerCanonicalCoefficients` for towers of schemes
defined only on the compact open levels satisfying a property `P`, using the
restricted colimit cohomology of
`Langlands.Shimura.RestrictedLevelTowerCohomology`. For a tower over a base
scheme `X`, each module sheaf `M` on `X` is pulled back to every level by the
actual inverse image along the projection. The result is a smooth
representation on the colimit cohomology over levels satisfying `P`, natural
in `M`, with pullbacks along morphisms of towers over `X` and an action of
any group acting on the tower by automorphisms over `X`. For a tower over all
levels, the module identifies these constructions for its restriction to the
levels satisfying `P` with the published ones over all levels. All
declarations are in namespace
`Langlands.Shimura.RestrictedLevelTowerCohomology`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, studies the cohomology of towers of Shimura varieties with the action
of the finite adelic group: after (3.5) on printed p. 307 for the prime-to-ℓ
finite adeles, and in Proposition 4.10 on printed p. 311 for `GG(A_f^{ℓ,p})`
as `K(N)^{ℓ,p}` varies. Moduli schemes for Shimura varieties are often
constructed only for sufficiently small levels, so such a tower is a functor
on a full subcategory of levels. The simplest coefficients are pulled back
from a base, such as constant coefficients on the Shimura varieties over
their field of definition. This module treats such coefficients for an
arbitrary tower over the levels satisfying `P`. Harris's passages are
motivation only; no statement from them is formalized.

The module constructs no Shimura varieties, no particular property of
levels, and none of Harris's automorphic coefficient systems, which are in
general not pulled back from the base. It constructs no Hecke-algebra action,
no finiteness, no compact support and no comparison with a limit scheme, and
it does not identify `p_K^* M` with a constant sheaf when `M` is constant.

## Inputs

Let `G : Type u` be a group with a topology and
`P : ObjectProperty (CompactOpenLevel G)`. Let
`T : P.FullSubcategory ⥤ Scheme.{u}` have `Etale (T.map a)` for every arrow
`a` between levels satisfying `P`. Let `X : Scheme.{u}`, let `R : Type u` be
a commutative ring, and let
`p : T ⟶ (Functor.const P.FullSubcategory).obj X` be the projections, with
components `p_K : T K ⟶ X` satisfying `T.map a ≫ p_L = p_K`. The projections
need not be étale.

The generic projection comparisons of the published module are used
unchanged: `LevelTowerCohomology.restrictionProjectionIso R q r f h`
identifies restriction along an étale `f` of `q^* M` with `r^* M` when
`f ≫ q = r`, and `LevelTowerCohomology.projectionCohomologyMap R q r f h n M`
is the resulting pullback `H^n(Z, q^* M) ⟶ H^n(Y, r^* M)`, with the published
congruence, identity, composition and naturality laws.

- The instances `etale_id_app`, `etale_comp_app` and `etale_iso_hom_app`
  state that identity morphisms, composites of morphisms with étale
  components, and isomorphisms of towers over the levels satisfying `P` have
  étale components.
- `baseCone p` is the same data as `p`, as a natural transformation from the
  constant diagram at `op X` to `T.op` (`baseCone_app_unop`).

## Generic additions

Assume that `G` is a topological group and `IsConjStable P`.

- `smoothColimitSectionsFunctor T R` is the colimit over levels satisfying
  `P` of global sections, as a functor from level-trivial coefficient
  diagrams to `SmoothRep R G`. It lifts the published
  `CoefficientDiagram.sectionsFunctor` into level-trivial presheaves by
  `isLevelTrivial_sections` and composes with
  `RestrictedLevelColimit.smoothFunctor P R`
  (`smoothColimitSectionsFunctor_obj`).
- `smoothColimitCohomologyZeroIso T R` identifies
  `smoothColimitCohomologyFunctor T R 0` with this sections functor, by the
  published `CoefficientDiagram.cohomologyZeroFunctorIso`.

## Pulled-back coefficients

Let `M` be a module sheaf on the small étale site of `X`.

- `canonicalCoefficients R p M` is the published geometric diagram
  `EtaleGeometricDiagram.canonicalCoefficients R (baseCone p) M`, transported
  by the published `CoefficientDiagram.toRestriction`. Its sheaf at `op K` is
  `p_K^* M` (`canonicalCoefficients_obj`), and its transition along `a` is
  `restrictionProjectionIso` at `M` (`canonicalCoefficients_map`), so the
  cohomology transition is `projectionCohomologyMap`
  (`canonicalCoefficients_cohomology_map`).
  `canonicalCoefficients_cohomology_obj` records that the degree `q`
  cohomology at level `K` is that of `T K` with coefficients `p_K^* M`.
- `canonicalCoefficients_map_congr` states that two arrows with the same
  scheme morphism have transitions differing by `restrictionCongr`.
- `canonicalCoefficientsFunctor R p` is the functor in `M`
  (`canonicalCoefficientsFunctor_obj`, `canonicalCoefficientsFunctor_map_app`).

## Level triviality and smooth representations

The hypothesis `hT` states
`T.map (restrictedSelfArrow P K k hk) = 𝟙 (T K)` for every level `K`
satisfying `P` and every `k ∈ K`.

- `isLevelTrivialCoefficients_canonical R hT M` proves that the pulled-back
  coefficients satisfy `IsLevelTrivialCoefficients`, using
  `canonicalCoefficients_map_congr`; no coefficient condition is assumed.
  `levelTrivialCanonicalCoefficientsFunctor R p hT` lifts
  `canonicalCoefficientsFunctor R p` into level-trivial coefficient diagrams.

Assume that `G` is a topological group and `IsConjStable P`.

- `smoothCanonicalCohomologyFunctor R p hT q` sends `M` to the colimit over
  shrinking levels satisfying `P` of `H^q(T K, p_K^* M)`, as a smooth
  representation of `G`, functorially in `M`
  (`smoothCanonicalCohomologyFunctor_obj`).
  `smoothCanonicalSectionsFunctor R p hT` is the analogue for global sections
  (`smoothCanonicalSectionsFunctor_obj`), and
  `smoothCanonicalCohomologyZeroIso R p hT` identifies the two in degree zero.
- `smoothCanonicalCohomology_ρ_ι_apply` states that `g` sends the image of a
  class `x` of level `K` to the image at level `restrictedConj P g K` of the
  pullback of `x` along `T.map (restrictedConjArrow P g K)`, followed by the
  coefficient transition of that arrow.
- `canonicalCohomology_exists_level` states, assuming also
  `IsDownwardClosed P` and `Nonempty P.FullSubcategory`, that every class
  comes from `H^q(T K, p_K^* M)` for a single level `K` satisfying `P`.

## Morphisms of towers and automorphism actions

Let `T'` and `T''` be further towers over the levels satisfying `P` with
étale level maps, let `φ : T' ⟶ T` and `ψ : T'' ⟶ T'` have étale components,
and let `hφ : φ ≫ p = p'` and `hψ : ψ ≫ p' = p''`.

- `canonicalPullback R p φ hφ M n` is the natural transformation of
  cohomology diagrams whose component at level `K` is
  `projectionCohomologyMap R p_K p'_K φ_K _ n M` (`canonicalPullback_app`).
  `canonicalPullbackNatTrans` makes it natural in `M`, and
  `canonicalPullback_id`, `canonicalPullback_comp` give the identity law and
  the composition law for `ψ ≫ φ`. `canonicalPullback_ι` states that the
  induced map of restricted colimits sends the image of a class of level `K`
  to the image of its pullback along `φ_K`.

Assume moreover that `G` is a topological group, `IsConjStable P`, and that
`T`, `T'`, `T''` satisfy level-triviality hypotheses `hT`, `hT'`, `hT''`.

- `smoothCanonicalPullback R p φ hφ hT hT' n` is the natural transformation
  `smoothCanonicalCohomologyFunctor R p hT n ⟶
  smoothCanonicalCohomologyFunctor R p' hT' n` whose component at `M` is
  `RestrictedLevelColimit.smoothFunctor P R` applied to `canonicalPullback`
  (`smoothCanonicalPullback_app`); it commutes with the action of `G`.
  `smoothCanonicalPullback_id` and `smoothCanonicalPullback_comp` are its
  laws, and `smoothCanonicalPullback_congr` states that equal tower
  morphisms give equal smooth pullbacks, whatever the witnesses of
  étaleness and of lying over `X`.
- `smoothCanonicalPullback_of_eq_id` and `smoothCanonicalPullback_of_eq_comp`
  restate these laws for endomorphisms of `T` over `X` equal to `𝟙 T` or to a
  composite `ψ ≫ φ`.
- For a group `Γ : Type v` and `ρ : Γ →* (Aut T)ᵐᵒᵖ` with
  `hρ γ : (ρ γ).unop.hom ≫ p = p`, `automorphismAction R p hT ρ hρ n M` is the
  object of `Action (SmoothRep R G) Γ` on
  `(smoothCanonicalCohomologyFunctor R p hT n).obj M` where `γ` acts by the
  smooth pullback along `(ρ γ).unop.hom` (`automorphismAction_ρ`). The
  opposite group is used as in the published module, because pullback is
  contravariant. `automorphismActionFunctor R p hT ρ hρ n` is the functor in
  `M`, and `automorphismActionForgetIso` identifies its underlying smooth
  representation functor. No topology on `Γ` is considered.

## Comparison with towers over all levels

Let `T₀ : CompactOpenLevel G ⥤ Scheme.{u}` be a tower over all levels with
projections `p₀ : T₀ ⟶ (Functor.const (CompactOpenLevel G)).obj X`.

- `restrictProjection P p₀ : P.ι ⋙ T₀ ⟶ (Functor.const P.FullSubcategory).obj X`
  has components `p₀.app K.obj` (`restrictProjection_app`).
- `etale_whiskerLeft_app` states that the restriction
  `Functor.whiskerLeft P.ι φ₀` of a tower morphism with étale components has
  étale components, and `restrictProjection_comp φ₀ hφ₀` states that it lies
  over the restricted projections when `φ₀ ≫ p₀ = p₀'`.
- `restrict_selfArrow hT₀` derives the restricted level-triviality hypothesis
  for `P.ι ⋙ T₀` from the published one for `T₀`.
- Assume that the level maps of `T₀` are étale.
  `restrictCoefficients_canonical` states, by `rfl`, that the restriction
  `restrictCoefficients` of the published
  `LevelTowerCohomology.canonicalCoefficients R p₀ M` is
  `canonicalCoefficients R (restrictProjection P p₀) M`.

Assume moreover that `G` is a topological group, `IsConjStable P`,
`IsDownwardClosed P`, `Nonempty P.FullSubcategory`, and that `hT₀` is the
published level-triviality hypothesis for `T₀`.

- `smoothCanonicalCohomologyRestrictIso R p₀ hT₀ q` is a natural isomorphism
  from `smoothCanonicalCohomologyFunctor R (restrictProjection P p₀)
  (restrict_selfArrow hT₀) q` to the published
  `LevelTowerCohomology.smoothCanonicalCohomologyFunctor R p₀ hT₀ q`. Its
  components are `smoothColimitCohomologyRestrictIso`, and its naturality is
  that of `smoothColimitCohomologyFunctorRestrictIso`.
  `smoothCanonicalCohomologyRestrictIso_hom_ι_apply` states that it sends the
  image of a class of level `K` to the image of the same class in the colimit
  over all levels.
- `smoothCanonicalPullback_restrictIso` states, for a morphism
  `φ₀ : T₀' ⟶ T₀` of towers over all levels with étale components, étale
  level maps of `T₀'`, its level-triviality hypothesis `hT₀'`, and
  `hφ₀ : φ₀ ≫ p₀ = p₀'`,
  that the restricted smooth pullback along `Functor.whiskerLeft P.ι φ₀`
  followed by the comparison for `p₀'` equals the comparison for `p₀`
  followed by the published `smoothCanonicalPullback` along `φ₀`. The proof
  is `RestrictedLevelColimit.map_colimitRestrictIso_hom` for the published
  `canonicalPullback`.
- `automorphismActionRestrictIso R p₀ hT₀ ρ₀ hρ₀ ρ hρ hρρ₀ n` concerns
  `ρ₀ : Γ →* (Aut T₀)ᵐᵒᵖ` over `X` and `ρ : Γ →* (Aut (P.ι ⋙ T₀))ᵐᵒᵖ` over
  the restricted projections with
  `hρρ₀ γ : (ρ γ).unop.hom = Functor.whiskerLeft P.ι (ρ₀ γ).unop.hom`. It is a
  natural isomorphism from `automorphismActionFunctor` for the restriction to
  the published `LevelTowerCohomology.automorphismActionFunctor`, in
  `Action (SmoothRep R G) Γ`, whose underlying morphisms are the components
  of `smoothCanonicalCohomologyRestrictIso`
  (`automorphismActionRestrictIso_hom_app_hom`).

## Provenance

This is an internal assembly of published results: the projection
comparisons and smooth pullbacks of `LevelTowerCanonicalCoefficients`,
`EtaleGeometricDiagram.canonicalCoefficients` and `toRestriction`,
`restrictionCongr`, the published `CoefficientDiagram` cohomology and
degree-zero identification, the restricted colimit cohomology and its
comparisons in `RestrictedLevelTowerCohomology` and
`RestrictedLevelColimit`, and Mathlib's `Aut`, `End` and `Action`. No
cohomology groups, actions, smoothness, compatibilities or functoriality laws
are supplied as input. Harris's passages are cited only as motivation.
