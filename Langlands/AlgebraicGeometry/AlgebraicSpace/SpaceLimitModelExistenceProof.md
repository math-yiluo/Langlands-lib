# Models of algebraic spaces along cofiltered limits of affine schemes: proof

Author: Worker 208.

The theorem `spaceLimitModelExistence` proves exactly
`Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitModelExistence` from
`SpaceLimitModelExistenceStatement`. It keeps the statement's arbitrary
universe and hypotheses: a cofiltered diagram of affine schemes with a limit
cone, and a separated algebraic space `Y` over the limit with a quasi-compact,
locally finitely presented atlas. This is a proof-only module: it changes
neither the statement nor anything the statement imports.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(31 December 2011), printed p.5 (Theorem 3.4(1)–(2)) and printed p.13,
registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Conrad
says the space case follows from the scheme case by étale descent. The proof
below spreads an étale presentation of `Y` to a stage using the scheme results.
It then takes the quotient of the spread relation with the Library's quotient
theorem for étale equivalence relations. Finally it compares base changes
through a common étale presentation.

## Plan of the proof

Choose an affine atlas `a : h_U ⟶ Y`. Refine a quasi-compact locally finitely
presented atlas by finitely many affine charts with `exists_affine_refinement`;
`U` is then affine, and locally of finite presentation over the limit.
`exists_closed_kernel_pair` gives the kernel pair `R` of `a`, with:

- projections `r₁, r₂ : R ⟶ U` that are étale;
- an equivalence relation on points (`AtlasRelation.IsEquivRel`);
- a pairing `R ⟶ U ×_{c.pt} U` that is a closed immersion.

The pairing is closed because `Y` is separated. The proof builds it from the
closed-immersion representation of the equality locus,
`exists_representsEqualizer_of_relative_diag`, and an isomorphism with the
kernel pair. In particular `R` is affine.

A *relation model* `RelModel c r₁ r₂ i` at a stage `i` consists of:

- affine schemes `VU`, `VR` over `D.obj i`, locally of finite presentation;
- pullback squares identifying their base changes to the limit with `U` and
  `R`;
- two maps `t, s : VR ⟶ VU` over the stage that base change to `r₁, r₂`.

`RelModel.restrict` base changes a relation model along a transition map. A
property of relation models is *stable* (`RStable`) if restriction preserves
it.

## Model calculus

- `exists_stage_lift`, `exists_model_hom`: a morphism over the limit between
  schemes with models at a stage comes from a morphism between the base-changed
  models at a later stage. The source model is affine and the target model
  locally finitely presented. The proof applies
  `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` to the diagram
  of base changes of the source model.
- `exists_eq_model`: two morphisms from an affine model to a scheme locally of
  finite type over the stage agree after restriction once they agree on the
  limit model. The proof uses
  `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`.
- `resHom` restricts a morphism over a stage along a transition map.
  `isPullback_resHom` shows the restriction is a base change, and
  `modelLift_resHom` gives compatibility with the limit comparisons.
- `isPullback_model_pullback`: base change commutes with fibre products of
  models, along any base map.
- Property descent for model morphisms (`exists_res_property`). The base change
  of a model morphism to the limit is the limit morphism up to the canonical
  isomorphisms (`baseChangeMap_cone_eq`). So a property that the Library proves
  descends along affine limits holds for a restriction:
  - flatness, by `AffineLimit.relativeFlatDescent` (`exists_res_flat`);
  - an open immersion diagonal, by `AffineLimit.relativeOpenImmersionDescent`
    applied to the diagonal (`exists_res_isOpenImmersion_diagonal`);
  - a closed pairing, by `AffineLimit.relativeClosedImmersionDescent`
    (`exists_res_closedImmersion_pairing`).

  In the last two cases, a restricted diagonal or pairing is compared with the
  restriction of the original one through the fibre-product isomorphism of
  `isPullback_model_pullback`. Étaleness follows in two restrictions
  (`exists_res_etale`): restrict to make the map flat, then again so that its
  diagonal is an open immersion. The map is then flat, formally unramified and
  locally finitely presented, hence étale (`Etale.of_formallyUnramified_of_flat`).

## Spreading the relation

`exists_relModel` produces a first relation model. It takes affine finitely
presented models of `U` and `R` with `SpaceLimitMorphisms.exists_model_of_affine_diagram`
and `exists_isAffine_model`, moves them to a common stage, and descends `r₁`
and `r₂` with `exists_model_hom`.

`exists_good_relModel` then restricts this model step by step. Each step keeps
the properties already gained, by the stability lemmas:

- `exists_etale_t`, `exists_etale_s`: étale projections, from étaleness of
  `r₁` and `r₂`.
- `exists_refMap`, `exists_symmMap`, `exists_transMap`: actual reflexivity,
  symmetry and transitivity maps, `RefMap`, `SymmMap` and `TransMap`.
  The reflexivity, symmetry and transitivity of `R` on points give limit maps:
  `U ⟶ R`, `R ⟶ R`, and `R ×_{r₂,U,r₁} R ⟶ R`. The proof descends these with
  `exists_model_hom`; the model of `R ×_U R` comes from
  `isPullback_model_pullback`. Their equations are made to hold with one
  application of `exists_eq_model`, into the fibre square of the atlas model.
  `TransMap.of_res` turns a map on a restricted fibre product into a
  transitivity map of the restricted model.
- Finally `exists_res_closedImmersion_pairing` makes the pairing
  `VR ⟶ VU ×_{D_j} VU` a closed immersion.

## The quotient and the comparison

`RelModel.relation` packages the final model as an `EtaleEquivalenceRelation`.
Its relation map into the absolute product `VU × VU` is a monomorphism: it
factors as the closed pairing followed by the monomorphism `VU ×_{D_j} VU ⟶
VU × VU`. The reflexivity, symmetry and transitivity fields come from the three
maps. The Library's `etaleEquivalenceRelationAlgebraicSpaceQuotient`, with base
map `qU`, gives an algebraic space `Q` over the stage. Its atlas `h_{VU} ⟶ Q`
is étale and surjective, and its kernel pair is the relation.

- **Separatedness.** `isSeparated_of_closed_relation` shows that a space is
  separated when, for an étale surjective atlas, the pairs of atlas points with
  equal image are cut out by a closed immersion into the square of the atlas
  scheme. For two sections over a test scheme, the proof passes to an étale
  cover on which both are atlas points. There, the locus is the pullback of the
  closed relation. The equality locus is fppf-closed
  (`sectionEqualizerSieve_isClosed`). The Library's `fppfClosedLocusDescent`
  (Stacks 03I0) then glues the local closed loci, in
  `exists_closed_representsEqualizer_of_fppf_local`. Finally
  `isClosedImmersion_diag_of_representsEqualizer` gives a closed diagonal.
- **The atlas.** The quotient atlas has structure map `qU`, which is locally of
  finite presentation and quasi-compact.
- **The comparison.** Base change the quotient atlas to the limit with
  `baseAtlas`, and compare it with the atlas of `Y` through the model
  isomorphism `VU ×_{D_j} c.pt ≅ U`. Two points of the common scheme have equal
  images in the base-changed quotient if and only if they have equal images in
  `Y`. Both conditions say that the pair lifts through the respective relation
  (`lift_of_isPullback`, `atlasSection_eq_of_isPullback`). Lifts translate
  through the model square of `R`. `commonEtalePresentationIso` gives an
  isomorphism of the étale sheaves, and the fully faithful forgetful functor
  `forgetToPresheaf` lifts it to an isomorphism of algebraic spaces.

## Scope

This proves only existence of a separated finitely presented model. It does
not prove uniqueness of models, morphism descent (proved separately as
`spaceLimitMorphismDescent`), descent of other properties, or any arithmetic
specialization.
