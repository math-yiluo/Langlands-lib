# Reverse recognized transport with a full-domain closed target

This internal construction uses published forward recognition and the actual
reverse locally refining subatlas to transport target recognized subsets
backward under a coherent strong quasi-isomorphism. Target closure under
local full domains is an explicit hypothesis.

The source context is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), Proposition 1.2.13 and Proposition 1.2.15 on printed pages 21–22
(PDF pages 18–19). This is derived infrastructure for recognized atlas
comparison, not a claim of the unrestricted propositions.

The inputs are actual indexed affinoid presentations `A` and `B` over a
complete ultrametric normed field, a strong map `f`, its full
quasi-isomorphism property `hf`, and the intrinsic original-map coefficient
coherence `hc`. The additional hypothesis
`hb : B.atlas.HasAllLocalDomains` says that every actual full local domain
of the target atlas is already an original target chart on its literal
locus. It is the existing closure property, not an assumed recognized
output or maximal-atlas comparison. The Library already proves this property
for actual constructed saturated atlases and full recognition atlases.
No source closure or directedness is required here.

The existing reverse chart selection consists of original target charts
contained in the entire image of an original source chart.
`reverseChartSelection_locallyRefining hb` proves that it is locally
refining; target full-domain closure also makes its subatlas full-domain
closed. The existing `reverseStrongMap hc hb` has the actual inverse
ambient homeomorphism and all constructed reverse bounded chart maps.
It is proved to be a quasi-isomorphism with intrinsic coefficient
coherence. These are previously constructed inputs to the new recognition
steps, not new assumptions about reverse maps.

For any `W : B.atlas.saturatedAtlas.RecognizedSubset`, first apply the
published forward subatlas recognition construction to obtain a recognized
presentation on this reverse selected atlas, with the same literal locus.
Next apply the published forward recognized-image construction of
`QuasiIsoRecognizedImage` to the constructed reverse map. The result is
`hf.reverseRecognizedImage hc hb W`, an actual recognized subset of
`A.atlas.saturatedAtlas`.

The elementary inverse-homeomorphism image identity proves

```text
(hf.reverseRecognizedImage hc hb W).locus = f.baseMap ⁻¹' W.locus.
```

Both recognition steps construct actual bounded inverse algebra maps.
Their composition defines

```text
hf.reverseRecognizedImageEquiv hc hb W :
  W.algebra ≃ (hf.reverseRecognizedImage hc hb W).algebra.
```

The two existing chart equations compose to give

```text
(hf.reverseRecognizedImage hc hb W).chart x =
  hf.inverseBaseMap
    (W.chart (hf.reverseRecognizedImageEquiv.spectrumHomeomorph x)).
```

The spectrum homeomorphism has the contravariant direction from the newly
constructed source recognized spectrum to the original target one. Both
algebra maps are constructed through finite full-domain descent and
canonical section algebras; the comparison is not recovered from spectrum
points.

`recognizedImageFunctor` sends each source recognized object to its forward
recognized image and each containment to the corresponding image
containment. `reverseRecognizedImageFunctor` uses the new reverse
recognized object and inverse-image containment. Their arrows are actual
recognized inclusion arrows, whose bounded algebra restrictions have
already been constructed in the respective original atlas.

Injectivity and surjectivity of the actual ambient homeomorphism prove
that both object round trips have the original literal loci.
`recognizedImageUnitComponent` and `recognizedImageCounitComponent`
use the canonical recognized inclusions in both directions on these
equal subsets. The proved uniqueness of recognized inclusions supplies
the inverse identities, naturality and equivalence triangle. Thus
`recognizedImageEquivalence` constructs

```text
A.atlas.saturatedAtlas.RecognizedSubset ≌
  B.atlas.saturatedAtlas.RecognizedSubset.
```

`recognizedAffinoidFamily_image` also proves equality of literal families
of subsets under the actual ambient map:

```text
(fun S => f.baseMap '' S) '' A.atlas.recognizedAffinoidFamily =
  B.atlas.recognizedAffinoidFamily.
```

One inclusion uses the forward constructed recognized objects; the other
uses the reverse constructed objects and the image-of-preimage identity.
The conditions do not exclude nonreduced algebras, trivial valuations,
general positive polyradii or empty spaces and domains.

This unit constructs reverse recognition, pointwise bounded algebra/chart
recovery and an equivalence of the actual recognized inclusion categories,
under explicit target closure. It does not assert naturality of these
chosen cross-atlas algebra comparisons or an isomorphism of their affinoid
diagrams. Removing the closure premise for arbitrary original presentations,
maximal-atlas uniqueness, the unrestricted analytic morphism description
and the analytic/equivariant sites remain separate obligations.
