# Full field points on small actual affinoid pushouts

This internal supporting unit treats a complete ultrametric normed base field
`K`, with independent base-field, spectrum-space and target-field universes
`u`, `v` and `uL`. Each presented algebra's actual Banach spectrum is supplied
with `Small.{v}`. The construction uses the actual small-spectrum presentation
and its saturation, retaining every full field-point evaluation and restriction
compatibility.

For a complete normed extension field `L`, `fieldPointCharacterEquiv` identifies
full field points of the saturated actual spectrum of `R` with bounded
`K`-algebra maps from `R` to `L`. It assumes
`DomainCompletedResidueSurjectivityStatement.{u}` explicitly. The proof
restricts to the retained original singleton chart, whose range is the whole
space and whose presented algebra equals `R`, and applies the existing
conditional global-chart character equivalence. Target algebraic closedness and
target ultrametricity are unnecessary for this equivalence.

`fieldPointCharacterEquiv_map` computes the actual field-point map induced by
`SmallAffinoidSpectrum.map f` as precomposition with `f`. The proof uses the
actual field-point bounded-evaluation formula. The original retained chart
pullback is heterogeneously equal to the original bounded map by the coherent
saturation-extension theorem; eliminating the two algebra equalities transports
that equation to the original algebras.

When `L` is also ultrametric and the actual affinoid pushout spectrum is
`v`-small, `pushout_fieldPoint_isPullback` proves that the actual full field-point
functor sends the square of the original left map, right map and the two
original bounded maps to a categorical pullback in types. The domain-residue
comparison remains a premise. Functoriality and the pushout condition give
commutation. Character naturality and the actual pushout's `hom_ext` prove
joint injectivity of the full point images. Compatible full points yield
compatible bounded characters; the actual pushout lift and the inverse
character equivalence construct a full point with both required full images.
`pushout_localizedFieldPoint_isPullback` rewrites the same result using the
actual localization and descended field-point functor.

The provenance is internal: these are consequences of the existing small
actual-spectrum construction, conditional global-chart character equivalence,
coherent saturation extension and bounded affinoid pushout universal property.
No finite or étale assertion is needed for this supplied-smallness result.
The unconditional preservation of arbitrary localized étale pullbacks remains
the larger task's unproved target.
