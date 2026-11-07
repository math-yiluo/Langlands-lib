# Canonical selected-chart maps over arbitrary original recognized algebras

Author: Worker 36.

For a locally refining selection of original charts, this module constructs
canonical full-domain maps from every original recognized affinoid algebra
to every contained selected-saturation chart algebra. It proves naturality
of the entire bounded maps and constructs a finite chart realization with
the unchanged original algebra and ambient chart.

## Source and provenance

This is derived infrastructure for Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), Proposition 1.2.13(i)–(ii),
printed p.21 / PDF p.18. The registered source is
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The cited original page was read; no source-specific errata file was
available in the Library notes.

Part (i) proves subnet invariance of the completed domain family using
finite subordinate covers. Part (ii) constructs canonical bounded
restrictions between contained affinoid domains of the extended atlas.
The present module combines the existing full-domain comparison for a
selected atlas with the original recognized-domain restrictions. Its
particular choices of saturation representatives, indices and finite
pushout overlaps are internal constructions. The source motivates their
role; it does not state these implementation-level definitions.

The inputs are the original indexed affinoid atlas `a`, a selection `P`,
its local refinement proof `hP`, and an arbitrary
`V : a.saturatedAtlas.RecognizedSubset`. Write `b = a.subatlas P hP`.
Recognition in `b.saturatedAtlas`, an algebra equivalence, and a compatible
family of output restrictions are not additional inputs.

## Canonical full domains for every contained chart

For `s : b.saturatedAtlas.Index`, take its actual local-domain
representative and forget the selection using `subatlasLocalDomain`.
`subatlasSaturatedOriginalIndex` uses its literal locus as an original
saturated index, denoted `S`. The theorem ending in `_range` identifies
the ranges of the original saturated chart at `S` and the selected
saturated chart at `s`.

`subatlasSaturatedToOriginal` is the actual equal-locus local-domain
inclusion `q` from the forgotten selected representative to the
representative chosen for `S` by the original saturation. The two
representatives can have different presentations. The inclusion stores
its full bounded restriction and its full represented relative domain.

Suppose the selected chart range at `s` lies in `V.locus`.
`subatlasRecognizedChartDomain` extends `q.relativeDomain` through
`V.originalDomain S`. This is a genuine full domain over `V.algebra`,
whose algebra is definitionally `b.saturatedAtlas.algebra s`.
Its structural bounded map is exactly

```text
q.restriction.comp (V.originalRestriction S containment).
```

The declarations ending in `_algebra` and `_baseMap` record these
definitional identities. No equality of algebra maps is inferred from
their values on spectrum points.

`subatlasRecognizedChartDomain_over_ambient` proves that the spectrum map
of this domain followed by `V.chart` is exactly the selected saturated
chart at `s`. The proof uses the composite spectrum map of domain
extension, the original-domain ambient equation and the ambient
naturality of `q`.

`subatlasRecognizedChartDomain_locus` identifies its locus as

```text
V.chart ⁻¹' range (b.saturatedAtlas.chart s).
```

The full representation's exact range supplies one containment.
Injectivity of the embedded `V.chart` identifies the spectrum points in
the converse containment, and the full representation gives membership.
Here pointwise reasoning identifies points and loci only.

## Naturality on the entire algebra

`subatlasRecognizedChartDomain_naturality` treats any contained selected
saturated charts `s` and `t` with the range at `s` inside the range at `t`.
If `R_s` and `R_t` denote their constructed domains, it proves

```text
b.saturatedAtlas.restriction s t containment |>.comp R_t.baseMap
  = R_s.baseMap.
```

For the proof, forget the actual selected saturated inclusion to an
original local-domain inclusion `f`. Let `g` be the original saturated
inclusion between `S` and `T`, and let `q` and `r` be their equal-locus
comparison inclusions. Both `f ≫ r` and `q ≫ g` are actual original
local-domain inclusions with the same source and target. The proved
uniqueness of such inclusions identifies them.

Taking their stored bounded restrictions and applying
`subatlasLocalDomainFunctor_map_restriction` gives an equality on all
algebra elements. The original recognized restriction naturality equation
then identifies the two composites from `V.algebra`. This establishes the
displayed full bounded-map equation, including on nilpotent elements.

## Finite realization and actual overlaps

The previous finite-refinement module supplies finitely many selected
saturated chart indices whose ranges cover exactly `V.locus`.
`subatlasRecognitionCanonicalComponent` applies the canonical construction
above to these indices. Its locus and ambient equations follow from the
general ones. The finite refinement supplies indices and coverage;
this module constructs the canonical component maps independently.

For components `E` and `F`, their intersection `E.inter F` is the actual
affinoid pushout quotient over `V.algebra`. Take its relative domain in
`E`, then extend this through the selected local-domain representative of
the first chart. `subatlasRecognitionOverlap` is the resulting actual
local domain of `b`; its algebra is that of the actual intersection.

`subatlasRecognitionOverlap_locus` proves that its ambient locus is
exactly the intersection of the two selected chart ranges. Extension
gives the image of the relative locus under the first ambient map.
The canonical ambient equation and `E.image_relative_locus` identify this
with the image under `V.chart` of `E.locus ∩ F.locus`. The canonical
preimage-locus equations give the required intersection, using that the
first chart range lies in `V.locus` for the reverse containment.

`subatlasRecognitionGluing` records the finite selected saturated chart
indices and the saturation indices of these actual overlap domains.
Its overlap-range fields use the preceding intersection equation.
`subatlasRecognitionGluing_locus` identifies its literal finite union
with `V.locus`.

Finally, `subatlasRecognitionAffinoidRealization` has algebra exactly
`V.algebra` and chart exactly `V.chart`. Its restrictions are the canonical
component base maps, with their full represented-domain properties.
To prove compatibility on an overlap, apply the general bounded
naturality equation to the overlap's saturated index and each of its
two containing charts. Both composites equal the same canonical map
from `V.algebra`. This proves equality of the complete overlap maps.

## Hypotheses and scope

The field is complete and ultrametric; its valuation may be trivial.
The field, ambient space and original atlas index have independent
universes. No global Hausdorffness, reducedness, nonzero-algebra or
nonempty-cover assumption is added.

This unit constructs full canonical maps and a finite realization for
every original recognized subset. The bounded equivalence between each
actual pushout overlap and its chosen saturated presentation, tensor-map
admissibility, specialness and recognition in the selected saturation
remain subsequent steps. Full recognized-category invariance, arbitrary
equivalent-net invariance, maximal-atlas uniqueness, analytic morphism
comparison, etale and equivariant sites, and the Harris specialization
remain further obligations of the host task.
