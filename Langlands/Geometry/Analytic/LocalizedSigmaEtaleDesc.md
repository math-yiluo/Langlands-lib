# Étale morphisms out of disjoint unions of analytic spaces

Module `Langlands.Geometry.Analytic.LocalizedSigmaEtaleDesc`.

This module proves the étale half of
`Langlands.Analytic.SaturatedAtlasPresentation.SigmaDescStatement`
(module `Langlands.Geometry.Analytic.LocalizedSigmaQuasiEtaleStatement`). If a morphism out of
the disjoint union `localizedSigma Y` of a family `Y j` of analytic spaces is étale on every
piece, then it is étale. The module states nothing about quasi-étale morphisms. All results are
internal lemmas about the Library's own constructions, so there is no literature source to cite.
The proofs combine published Library results as described below.

## Original level: component inclusions of a disjoint union of atlases

Namespace `Langlands.Analytic.AtlasDisjointUnion`. Here `A : I → AffinoidAtlasPresentation K` is
a family of atlas presentations with nonempty charts, and `presentation A hA` is their disjoint
union.

- `isEtaleAtAllPieces_of_compatibleInclusion_comp`: let `g` be a strong map out of the
  saturation of the disjoint union, and let `x` be a point of component `i`. If the saturated
  composite of the inclusion of component `i` with `g` is étale at all pieces at `x`, then `g`
  is étale at all pieces at `⟨i, x⟩`. This applies the published
  `StrongHom.IsDomainEmbedding.IsEtaleAtAllPieces.of_precomp_domainEmbedding` to three inputs:
  - the fact that the strong inclusion `inclusionStrong A hA i` of a component is a domain
    embedding (`AtlasDisjointUnion.isDomainEmbedding_inclusionStrong`, from the module
    `Langlands.Geometry.Analytic.DisjointUnionDomainEmbeddings`);
  - the coherent pullbacks of the compatible inclusion (`(compatibleInclusion A hA i).coherent`);
  - the fact that `Sigma.mk i` is an open embedding (`Topology.IsOpenEmbedding.sigmaMk`).

## Saturated level: the chosen disjoint union

Namespace `Langlands.Analytic.SaturatedAtlasPresentation`.

- `strongEtale_of_sigmaCofan_inj`: a morphism `h : sigmaPresentation T ⟶ B` of saturated
  presentations is `strongEtale` if every composite `(sigmaCofan T).inj j ≫ h` is. The proof
  has three steps:
  1. Compose with the inverse of the comparison isomorphism `saturationFunctorIso B`. This is a
     quasi-isomorphism (`isQuasiIso_of_isIso`), so it changes neither side
     (`strongEtale_postcomp_quasiIso_iff`).
  2. Source and target are now constructed saturations, so `strongEtale_ofSaturation_iff`
     turns both the hypothesis and the goal into `StrongHom.IsEtaleAllPieces`. That is a
     pointwise condition on the points `⟨j, x⟩` of the disjoint union.
  3. At each point, apply `isEtaleAtAllPieces_of_compatibleInclusion_comp`. The cofan
     inclusion `(sigmaCofan T).inj j` is the saturation of the compatible component inclusion,
     and composition of saturated presentations is `saturatedComp`.

## Localized level: the étale half of the statement

- `etale_sigmaDesc`: for `Y : J → LocalizedCategory` and `f : ∀ j, Y j ⟶ Z` with every `f j`
  étale, the morphism `Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan Y) f` is étale.

  By definition, the coproduct `isColimitLocalizedSigmaCofan Y` is the original cofan of the
  Library's `rightFractionCoproducts K J`. Its descended morphism is therefore definitionally
  `R.localizedDesc T φ`, where:
  - `T j = localizedObjectEquiv.symm (Y j)`;
  - `φ j = L.map (R.π (T j)) ≫ f j`.

  The proof unfolds `localizedDesc` into the composite of three morphisms:
  1. the inverse of the isomorphism given by the denominator;
  2. `L.map (descNumerator T φ)`;
  3. the isomorphism `L.objObjPreimageIso Z`.

  Isomorphisms are étale (`etale_of_isIso`) and étale morphisms compose (`etale_comp`), so only
  the middle factor needs an argument. By `etale_localizationFunctor_map_iff_strongEtale` it
  suffices that `descNumerator T φ` is `strongEtale`. By `strongEtale_of_sigmaCofan_inj` it
  suffices to check each component, and on component `j` the numerator restricts to
  `R.π _ ≫ (fraction W L (φ j)).f` (`Cofan.IsColimit.fac`). The map `R.π _` is the
  quasi-isomorphism `nonemptyReplacementHom` (`isQuasiIso_nonemptyReplacementHom`), so it can be
  dropped (`strongEtale_precomp_quasiIso_iff`).

  Going back through `etale_localizationFunctor_map_iff_strongEtale`, it remains to show that
  `L.map (fraction W L (φ j)).f` is étale. The defining property `fraction_spec` of the chosen
  fraction, together with `MorphismProperty.RightFraction.map`, gives
  `L.map fr.f = L.map fr.s ≫ φ j ≫ (L.objObjPreimageIso Z).inv`. In this composite:
  - `L.map fr.s` is an isomorphism, because `fr.s` is a quasi-isomorphism.
  - `φ j` is the isomorphism `L.map (R.π (T j))` followed by the étale morphism `f j`.
  - The last factor is an isomorphism.

  The composite is therefore étale.
