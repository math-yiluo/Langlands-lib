# Pullbacks of patch-preserving endomorphisms to an affinoid model

Module `Langlands.Geometry.Analytic.AffinoidPatchPullback`, namespace
`Langlands.Analytic.SaturatedAtlasPresentation`. Here `X` is an object of the
localized analytic category `LocalizedCategory.{u, v, v}` over a complete
ultrametric normed field `K`.

## Purpose and provenance

This is an internal prerequisite for the proofs in
`CompactPullbackContinuityOfSmall` of `CompactPullbackActionContinuitySmallStatement`
and, under `UnivLE.{u, v}`, of `CompactPullbackActionContinuityStatement`. No
literature statement is
transcribed. Take an analytic domain `E` of `X` (a "patch") together with an
affinoid model of it, meaning a saturated presentation `S₀` with a greatest
chart `t` and an isomorphism
`ι : localizationFunctor.obj S₀ ≅ domainObj X E`. An endomorphism of `X` that
maps `E` into itself then induces a bounded endomorphism of the algebra of
the chart `t`. Later modules use this to transport those members of a group
action on `X` that preserve `E` to bounded endomorphisms of the affinoid
algebra of the model. The construction uses only the Library's `domainRestrict`
(analytic domains as objects), `localizedTopTargetHomEquiv`
(`TopChartSpectralTests`, which recovers a complete strong map from a
localized arrow into a presentation with a greatest chart) and
`AffinoidAtlasPresentation.StrongHom.pullbackAtTop` (`AffineTopChartPullbacks`).

## Declarations

- `mapsTo_of_preimage_eq E h`: if `map φ ⁻¹' E.carrier = E.carrier`, then `φ`
  maps `E.carrier` into itself.
- `patchConj E ι φ h`, for `φ : X ⟶ X` mapping `E` into itself (`h`): the
  endomorphism `ι.hom ≫ domainRestrict E E φ h ≫ ι.inv` of
  `localizationFunctor.obj S₀`, i.e. `φ` restricted to the patch and conjugated
  to the model.
- `patchPullback E t ht ι φ`: a bounded `K`-algebra endomorphism of
  `S₀.presentation.atlas.algebra t`. If `map φ ⁻¹' E.carrier = E.carrier`, it
  is the pullback at the greatest chart `t` of the complete strong map
  `(localizedTopTargetHomEquiv t ht).symm (patchConj E ι φ _)`. Otherwise it
  is the identity. The default value only makes `patchPullback` a total
  function of `φ`, so that it can be applied to a whole family `σ g` and
  compared with the identity along a filter. Every later use is restricted to
  the eventual set where the preimage equation holds.
- `patchPullback_of_preimage_eq`: the defining equation in the case where the
  preimage equation holds.

The hypothesis `ht` says that `t` is a greatest chart of `S₀`: every chart of
`S₀` has range inside the range of `t`.
