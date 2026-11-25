# Good charts inside a patch with an affinoid model

Module `Langlands.Geometry.Analytic.AffinoidPatchGoodCharts`, namespace
`Langlands.Analytic.SaturatedAtlasPresentation`.

The field `K : Type u` is complete, normed and ultrametric. `X` is an object of
the localized analytic category `LocalizedCategory.{u, v, v}`. The group
`G : Type z` carries an arbitrary topology, and `σ : G →* Aut X` is an action.

## Setting

A *patch with an affinoid model* consists of:

- an analytic domain `E` of `X`;
- a saturated presentation `S₀` with a greatest chart `t`. The hypothesis
  `ht` says that every chart of `S₀` has range inside the range of `t`;
- an isomorphism `ι : localizationFunctor.obj S₀ ≅ domainObj X E`.

For an endomorphism `φ` of `X` that preserves `E`, `patchPullback E t ht ι φ`
(module `AffinoidPatchPullback`) is the bounded endomorphism of the chart
algebra `S₀.presentation.atlas.algebra t` induced by `φ` restricted to `E` and
conjugated by `ι`. For other `φ` it is the identity.

## Main theorem

`isGoodChart_of_affinoidPatch hE hconv W hW : IsGoodChart σ W` assumes:

- `hE`: for `g` near `1`, `σ g` preserves the patch. In Lean,
  `localizedSpaceFunctor.map (σ g).hom ⁻¹' E.carrier = E.carrier` eventually
  in `𝓝 1`;
- `hconv`: for every `a` in the model's chart algebra,
  `SpectralConvergesOn (𝓝 1) (fun g => patchPullback E t ht ι (σ g).hom)
  (BoundedAlgHom.id K _) a`;
- `W` is a chart of `presentationOf X`, and `hW` says its range lies in
  `E.carrier`.

It concludes that `W` is a good chart for `σ` in the sense of `IsGoodChart`
(module `GoodChartContinuity`). That is, the members of `σ` near `1` preserve
the chart, and their chart pullbacks `preservedChartPullback W (σ g).hom`
converge spectrally to the identity on every section of the chart algebra.

No smallness hypothesis is needed. The patch, the model and the chart all
live in the universes of `X`.

## Declarations

- `domainRestrict_apply_val`: the restriction of an endomorphism to a domain
  acts on points as the endomorphism.
- `patchModelMap E t ht ι : (presentationOf X).domain E ⟶ S₀` is the complete
  strong map `(localizedTopTargetHomEquiv t ht).symm ι.inv`.
  `localizationFunctor_map_patchModelMap` says that its localization is
  `ι.inv`.
- `isQuasiIso_patchModelMap`: the model map is a strong quasi-isomorphism.
  Its localization `ι.inv` is an isomorphism, and the Library theorem
  `isQuasiIso_of_isIso_localizationFunctor_map` (module
  `SaturatedLocalizedIsomorphisms`) applies.
- `patchChart W hW` is the chart `W` viewed as a chart of the patch's
  presentation, i.e. the index `⟨W, hW⟩`.
- `patchChartDomain E t ht ι W hW` is a `Domain` (a full represented affinoid
  domain, module `GeneralizedAffinoid/Domain`) of the model's chart algebra.
  Its algebra is the chart algebra of `W`. Its structural map is the pullback
  `(patchModelMap E t ht ι).pullbackAtTop t ht (patchChart W hW)`. Its locus
  is the image of the chart `W` in the coordinates of `t`,
  `(patchModelMap E t ht ι).chartImageLocus (patchChart W hW) t`. The
  representation property is the second clause of the quasi-isomorphism
  property. This is the same data as the Library's `IsQuasiIso.localDomain`
  (module `StrongAtlasQuasiIsomorphisms`) for that chart pair, written out
  explicitly.
- `mem_range_chart_iff_mem_patchChartDomain_locus`: a point `y` of the patch
  lies on the chart `W` exactly when its coordinate `x` on the chart `t` of the
  model lies in the locus of `patchChartDomain`. The proof uses injectivity of
  the model map's base map.
- `patchModelMap_baseMap_restrict`: the model map intertwines the restriction
  of a patch-preserving endomorphism with the strong endomorphism of the model
  whose localization is `patchConj E ι φ _`.
- `pullbackAtTop_domainMap_comp_patchModelMap`: the structural map of
  `patchChartDomain` equals the greatest-chart pullback of the composite of the
  strong inclusion of the chart domain of `W` into the patch with the model
  map. The proof uses `saturatedComp_pullback` and `restriction_id`.
- `preservedChartPullback_comp_patchChartDomain_baseMap φ hW hE hC`: suppose
  `φ` preserves both the patch (`hE`) and the chart domain of `W` (`hC`). Then
  `(preservedChartPullback W φ).comp D.baseMap =
  D.baseMap.comp (patchPullback E t ht ι φ)`, where
  `D = patchChartDomain E t ht ι W hW`. The two strong endomorphisms, of the
  chart domain and of the model, commute with the composite map of the
  previous item after localization. This is checked after composing with the
  mono `domainι X E`. Then `pullbackAtTop_comp` is applied to both sides.
- `eventually_preimage_chartDomain_of_affinoidPatch hE hconv W hW`: eventually
  in `𝓝 1`, `σ g` preserves the chart domain of `W`. For a point of the patch,
  `patchModelMap_baseMap_restrict` moves the question to the model's chart
  `t`. There `Domain.eventually_comap_mem_locus_iff` (module
  `GeneralizedAffinoid/DomainSpectralConvergence`) keeps the locus of
  `patchChartDomain` stable under the converging pullbacks, uniformly in the
  spectrum point. A point outside the patch lies on neither side, because
  `σ g` preserves the patch and `W` lies inside it.
- `spectralConvergesOn_preservedChartPullback_of_affinoidPatch hE hconv W hW a`:
  the chart pullbacks on `W` converge spectrally to the identity. The proof
  applies `Domain.spectralConvergesOn_of_factor` to `patchChartDomain`. The
  limit map is the structural map `D.baseMap`, the moving maps are
  `(preservedChartPullback W (σ g).hom).comp D.baseMap`, and the
  factorizations through `D` are the chart pullbacks themselves. Convergence
  of the moving maps follows from `hconv`, postcomposed with `D.baseMap`
  (`SpectralConvergesOn.postcomp`), together with the eventual commutation
  of the previous items.
- `isGoodChart_of_affinoidPatch`: the pair of the last two results.

## Provenance and scope

This module is internal. It is a prerequisite for the proofs in
`CompactPullbackContinuityOfSmall` of `CompactPullbackActionContinuitySmallStatement`
and, under `UnivLE.{u, v}`, of `CompactPullbackActionContinuityStatement`, and
transcribes no literature statement. In these proofs the patches are pair-chart patches `p⁻¹ U ∩ q⁻¹ V` of
the pullback, modelled on affinoid pushouts (modules
`PairChartPatch`, `AffinoidPatchPullback` and `PairChartConvergence`). This
module turns convergence on such a model into good charts. The criterion
`isContinuousAction_of_locallyGood` (module `LocallyGoodChartContinuity`)
then gives continuity.
