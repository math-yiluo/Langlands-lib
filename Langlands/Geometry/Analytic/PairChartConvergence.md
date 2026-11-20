# Spectral convergence of a pullback action on pair charts

Module `Langlands.Geometry.Analytic.PairChartConvergence`, namespace
`Langlands.Analytic.SaturatedAtlasPresentation`. It builds on the pair
charts of `PairChartPatch` and the patch pullbacks of `AffinoidPatchPullback`.

## Purpose and provenance

This is an internal prerequisite for Task 7765
(`CompactPullbackActionContinuityStatement`). No literature statement is
transcribed. Mathematically: a fibre product `P = U ×_B V` carries an action
`σ` whose projections `p`, `q` are equivariant for continuous actions `σU`,
`σV`. Over a pair of compatible charts, the part of `P` lying over both is
the affinoid space of the pushout algebra `A_U ⊗̂_{A_B} A_V`. Near the
identity, the action on this part is pulled back to bounded endomorphisms of
that algebra, and these converge spectrally to the identity. The proof
checks this on the two families of generators coming from `A_U` and `A_V`,
where it reduces to the continuity of `σU` and `σV`.

Library results used: `AffinoidPushout.spectralConvergesOn_of_factors`
(`AffinoidPushoutSpectralTests`); `IsContinuousAction.spectralConvergesOn_preservedChartPullback`,
`preservedChartPullback_of_preimage_eq` and `chartDomainPullback`
(`ChartDomainSpectralTests`); `eventually_preimage_eq_pullback_patch`
(`PullbackActionTests`); `pullbackAtTop_comp` (`AffineTopChartPullbacks`);
`smallSpectrumIso_hom_pullbackAtTop` and `chartSpectrum_small`
(`SaturatedTopChartComparison`); `SmallAffinoidSpectrum.topIndex`,
`top_contains`, `top_algebra` and `map_pullbackAtTop_heq`
(`SmallAffinoidPullbacks`); `localizationFunctor_map_injective`
(`LocalizedPullbackDescent`); `BanachSpectrum.SpectralBound.map`.

## Declarations

General helpers:

- `boundedAlgHom_transport_comm`: a bounded algebra map `φ'` that is `HEq` to `φ`
  after equalities `R' = R`, `S' = S` of presented algebras satisfies
  `φ'.comp (eqToHom _) = (eqToHom _).comp φ`. This restates, publicly, a
  private Library lemma of `SaturatedTopChartComparison`.
- `spectralConvergesOn_of_transport`: for an equality `h : A' = A`, spectral
  convergence of endomorphisms `Φ t` of `A'` to the identity follows from
  convergence of `(Φ t).comp (eqToHom h.symm)` to `eqToHom h.symm` on `A`.
- `localizationFunctor_map_localizedTopTargetHomEquiv_symm`: the localization
  of the strong representative `(localizedTopTargetHomEquiv j hj).symm φ` is
  `φ`.
- `IsContinuousAction.eventually_preimage_chartDomain`: for a continuous
  action `σX` and a chart `i`, near the identity `σX a` has the chart domain
  of `i` as exact preimage.

For `c : PairChartData f g` with `Small.{v} (BanachSpectrum c.algebra)`:

- `top`, `top_contains`, `top_algebra`: the whole-spectrum chart of the pair
  chart `c.obj` is a greatest chart, and its algebra equals `c.algebra`.
- `strongFst`, `strongSnd`, `fst_eq`, `snd_eq`: the complete strong
  projections whose localizations are `c.fst`, `c.snd`.
- `fstTop`, `sndTop`: the projections on greatest charts, which are bounded
  maps from the left (right) chart algebra to the algebra of `c.top`.
  `fstTop_eq` and `sndTop_eq` identify them with the pushout legs
  `AffinoidPushout.leftMap`, `AffinoidPushout.rightMap`, transported along
  `top_algebra`.
- `eventually_preimage_patch`: if `σU`, `σV` are continuous and `p`, `q` are
  equivariant, then near the identity `σ a` has the patch `c.patch p q` as
  exact preimage.

Assuming moreover `hP : IsPullback p q f g`:

- `patchConj_fst`, `patchConj_snd`: if `φ ≫ p = p ≫ φU`, `φ` preserves the
  patch and `φU` preserves the left chart domain, then
  `patchConj (c.patch p q) (c.patchIso hP) φ _ ≫ c.fst = c.fst ≫ domainRestrict _ _ φU _`.
  The same holds on the right.
- `patchPullback_comp_fstTop`, `patchPullback_comp_sndTop`: under exact
  preimage hypotheses, the patch pullback of `φ` intertwines `fstTop` with
  `preservedChartPullback c.left φU`, i.e.
  `(patchPullback _ c.top c.top_contains (c.patchIso hP) φ).comp c.fstTop =
  c.fstTop.comp (preservedChartPullback c.left φU)`. The same holds on the
  right.
- `spectralConvergesOn_patchPullback` (main result): for continuous `σU`,
  `σV` and equivariant `p`, `q`, every element `x` of the algebra of `c.top`
  satisfies
  `SpectralConvergesOn (𝓝 1) (fun a => patchPullback (c.patch p q) c.top c.top_contains (c.patchIso hP) (σ a).hom) (BoundedAlgHom.id K _) x`.

## Proof outline

`patchConj_fst` is a diagram chase. Cancel the monomorphism
`domainι U c.leftDomain`, then use `fromPatch_fst`, `patchFst_comp`,
`domainRestrict_comp`, the equivariance `φ ≫ p = p ≫ φU` and `toP_fst`.

`patchPullback_comp_fstTop` lifts this equation to complete strong maps:
both sides are strong maps into a presentation with a greatest chart, and
the localization functor is injective on morphisms. It then applies
`pullbackAtTop_comp` to both sides.

`fstTop_eq` uses `strongFst = pushoutFst ≫ (smallSpectrumIso _ _).hom`, then
`pullbackAtTop_comp` and `smallSpectrumIso_hom_pullbackAtTop`. Finally it
transports the `HEq` statement `map_pullbackAtTop_heq` with
`boundedAlgHom_transport_comm`.

For the main result, transport along `top_algebra` reduces the claim to the
affinoid pushout `c.algebra`. There `spectralConvergesOn_of_factors` reduces
it to elements `leftMap y` and `rightMap y`. Take `y` on the left. Eventually,
`σ a` preserves the patch (`eventually_preimage_patch`) and `σU a` preserves
the left chart. On that set, `patchPullback (σ a)` sends `fstTop y` to
`fstTop (preservedChartPullback c.left (σU a) y)`. The spectral displacement
of `fstTop y` is therefore the image under `fstTop` of the displacement of
`y`. It is bounded by `ε` eventually, by the continuity of `σU`
(`spectralConvergesOn_preservedChartPullback`) and `SpectralBound.map`.
