# Recognized images under coherent strong quasi-isomorphisms

This internal construction transports an arbitrary recognized subset of the
full source atlas to an actual recognized subset of the full target atlas.
It constructs finite realization data over the unchanged source recognized
algebra and the transported ambient chart, then derives intrinsic target
recognition and bounded algebra recovery.

The source context is Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), Proposition 1.2.13 and Proposition 1.2.15 on printed pages 21–22
(PDF pages 18–19). The implementation is derived infrastructure for general
atlas comparison; it does not claim the full propositions.

The input is an actual strong map `f : StrongHom A B`, a proof
`hf : f.IsQuasiIso`, the intrinsic original-map coefficient coherence
`hc : f.HasCoherentPullbacks`, and an arbitrary recognized subset `V` of
`A.atlas.saturatedAtlas`. The field is complete and ultrametric; ambient
and original index universes are independent. The input supplies no target
recognition or section-algebra comparison.

For a source saturated chart `s`, take the actual local-domain image
already published in `StrongQuasiIsoDomainImage` of its chosen source representative.
Its algebra is unchanged and its literal locus is the image under `f`.
`saturatedImageIndex`, denoted `S(s)`, makes this target local-domain locus
a target saturated index. The range theorem proves

```text
range (B.atlas.saturatedAtlas.chart S(s)) =
  f.baseMap '' range (A.atlas.saturatedAtlas.chart s).
```

The actual bounded equivalence `saturatedImageEquiv`, denoted `e_s`, compares
the unchanged source saturated algebra with the representative chosen by the
target saturation. Full target local-domain inclusion uniqueness constructs
both of its maps. The ambient equation combines the inverse local-domain
inclusion with the actual image-chart equation of the preceding module.

For every source saturated containment `s ⊆ t`,
`saturatedImageEquiv_naturality` proves

```text
r_target(S(s), S(t)) ∘ e_t = e_s ∘ r_source(s, t)
```

as an equality of entire bounded maps. The two inverse comparison triangles
are arrows between the same target local domains. Their equality follows
from the full represented-domain uniqueness theorem. The image functor
retains the original source restriction exactly, giving the displayed
equation without using spectrum faithfulness.

For every source chart `s` contained in `V.locus`,
`recognitionImageChartDomain` is a full domain over the unchanged `V.algebra`.
It has target saturated algebra at `S(s)`, bounded base map
`e_s ∘ V.originalRestriction s`, and locus the inverse image of the target
chart range under `f.baseMap.comp V.chart`. The range theorem and injectivity
of the ambient homeomorphism identify this locus with the original component
locus in `V` coordinates. Transport by the actual bounded equivalence
(`Represents.postcomp_equiv`) proves the full universal property, including
all positive-polyradius affinoid tests.

The component ambient-chart equation follows from the original recognized
restriction equation and the equation for `e_s`. The complete bounded
naturality equation follows from the displayed saturated comparison and
the existing full naturality of the source recognized restrictions.

`recognitionImageGluing` transports `V.property.cover` and all its overlap
indices through `S`. Injectivity of `f.baseMap` proves that images preserve
the exact pairwise intersection equations. Commutation of images with the
finite indexed union proves that the new literal union is
`f.baseMap '' V.locus`.

`recognitionImageAffinoidRealization` uses exactly `V.algebra` and the chart
`f.baseMap.comp V.chart`. The actual ambient homeomorphism makes this chart
an embedding. The transported full component representations and complete
bounded naturality prove all realization fields, including overlap
compatibility; no target algebra-recovery output is supplied.

The generic construction in `AffinoidRealizationSpecialCover` derives
specialness, including genuine completed-tensor overlap admissibility and
Hausdorffness of the literal union. It then constructs all three intrinsic
recognition conditions. `recognizedImage` is the resulting actual target
recognized subset. The final statements give

```text
(hf.recognizedImage hc V).locus = f.baseMap '' V.locus

hf.recognizedImageEquiv hc V :
  V.algebra ≃ (hf.recognizedImage hc V).algebra

(hf.recognizedImage hc V).chart x =
  f.baseMap (V.chart (hf.recognizedImageEquiv.spectrumHomeomorph x)).
```

The bounded maps in both directions are obtained through actual finite
full-domain descent and the canonical section algebras. The construction
does not impose reducedness, a nontrivial valuation, nonempty components,
directedness or full-domain closure of the original atlases.

This proves forward recognized-image existence and actual algebra/chart
recovery for every coherent strong quasi-isomorphism. Reverse transport,
naturality of these chosen recognized algebra comparisons, an equivalence
of recognized categories for arbitrary such atlas comparisons,
maximal-atlas uniqueness and the analytic/equivariant sites remain separate
obligations.
