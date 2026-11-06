# Constructed idempotence of full affinoid recognition

Author: Worker 36.

This module proves that iterating full affinoid recognition adds no
literal affinoid chart range. For each chart in the iterated atlas, it
constructs a chart of the earlier full recognition atlas on exactly the
same ambient subset. It also constructs an actual bounded equivalence
between their presented algebras and proves the exact ambient-chart
formula through its spectrum homeomorphism.

The source motivation is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), the special-subset and special-cover definitions
before Lemma 1.2.12, printed p.20 / PDF p.17; and the recognition
conditions and Proposition 1.2.13(iii), including the flattening of finite
defining covers in its proof, printed p.21 / PDF p.18. Registered source
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These original pages were read for the construction. No source-specific
errata file was found in the available project and Library locations.

The result is a derived construction of literal chart-family idempotence
for the actual full recognition operation. The finite original-chart
coverage, canonical full maps, pushout overlaps and completed-tensor
admissibility are all constructed. It does not assume an earlier
recognition of the iterated chart or identify algebra maps from their
spectrum values. Naturality of the final algebra equivalences as an
atlas-level comparison and invariance under arbitrary equivalent nets
remain separate from the precise conclusion proved here.

Put `B = a.fullRecognitionAtlas` and take
`W : B.saturatedAtlas.RecognizedSubset`, an index of
`B.fullRecognitionAtlas`. The existing finite flattening supplies
finitely many indices in `a.saturatedAtlas` whose chart ranges cover
`W.locus`. `iteratedRecognitionChartIndex_subset` records that each
component range is contained in that same literal locus.

`iteratedRecognitionCanonicalComponent` applies the canonical
nested-recognition original-domain construction to each of these indices.
Each is an actual full domain over `W.algebra`, with its original chosen
first-saturation algebra unchanged. Its ambient theorem recovers the
original first-saturation chart under `W.chart`, and its locus is exactly
the inverse image of that chart range.

These canonical maps have proved entire original-chart restriction
naturality through the nested atlases. The finite flattening is used for
its actual component indices and finite coverage. The construction does
not need to identify its initially flattened structural maps with these
canonical maps.

For canonical components `E` and `F`, `iteratedRecognitionOverlap` forms
their actual full-domain intersection over `W.algebra`. This is the
affinoid pushout quotient of their complete structural bounded maps. It
regards the intersection as a relative domain over `E.algebra` using the
left pushout leg and extends it through the original local representative
of the first saturated chart. Its algebra is therefore literally the
actual intersection quotient.

`iteratedRecognitionOverlap_locus` proves that this local domain has
exactly the ambient intersection of the two component chart ranges.
The proof uses the actual relative-image formula and the component
ambient-map recovery. For the reverse inclusion, containment of the
first chart in `W.locus` supplies a parent spectrum point. No Hausdorff
hypothesis on the ambient space is needed.

`iteratedRecognitionGluing` uses the first-saturation component indices
and the literal overlap loci as actual first-saturation overlap indices.
Its locus theorem identifies the finite union with `W.locus`.
`iteratedRecognitionAffinoidRealization` constructs every realization
field with parent algebra `W.algebra` and parent chart `W.chart`.
All component maps and full represented-domain properties are the
canonical ones just constructed.

Entire bounded overlap compatibility follows by applying canonical
original-chart naturality to the inclusion of the overlap chart into
each component. Both composites are the same canonical map from
`W.algebra` to the chosen overlap algebra. Thus no overlap compatibility
or section-algebra comparison is supplied as an extra hypothesis.

`iteratedRecognitionOverlapEquiv` is the actual bounded equivalence
from the unchanged pushout quotient to the representative chosen for
that literal overlap locus. The left-restriction theorem identifies the
stored atlas restriction with this equivalence composed with the actual
left pushout leg. It uses the equal-locus local-domain comparison and
the actual extension inclusion; full local-domain uniqueness identifies
their composite with the saturated inclusion.

The right-restriction theorem cancels the full structural map of the
second component. After cancellation, the realization's complete
compatibility equation, the left-leg identity and the pushout relation
prove equality with the right pushout leg under the same equivalence.
All these are equalities of bounded algebra maps on arbitrary elements.

`iteratedRecognitionGluing_overlapTensorMap` applies the genuine
completed tensor's full bounded-map uniqueness theorem to both leg
identities. It identifies the exact stored tensor overlap map with the
actual pushout tensor quotient followed by the constructed bounded
equivalence.
`iteratedRecognitionGluing_tensor_isAdmissibleEpi` composes the actual
pushout quotient's admissibility with admissibility of the bounded
equivalence, whose inverse supplies a bounded section. This proves
surjectivity and the positive uniform comparison between the quotient
seminorm and the unchanged target norm.

`iteratedRecognitionGluing_isSpecialCover` combines these tensor
properties with the Hausdorff topology supplied by the actual parent
spectrum homeomorphism. Compactness already follows from the finite union
of actual affinoid component charts. `iteratedRecognitionSpecialSubset`
therefore constructs a literal special subset of `a.saturatedAtlas`
on precisely `W.locus`.

`fullRecognitionIdempotenceIndex` applies the existing realization
recognition-transfer construction to these actual data. It supplies all
three intrinsic recognition conditions and constructs an index of the
earlier `a.fullRecognitionAtlas` on the unchanged literal locus.
No affinoid section presentation, canonical-map bijectivity or full
component-domain condition is supplied as an output assumption.

`fullRecognitionIdempotenceAlgebraEquiv` composes the constructed
parent/sections bounded equivalence with the inverse of the new
recognition witness's presentation/sections equivalence. It compares
the actual `W.algebra` with the specific earlier-atlas presentation
selected by this new recognition witness. Both directions are bounded
algebra maps with proved inverse identities.

`fullRecognitionIdempotenceIndex_chart` applies the general chart
comparison valid for any intrinsic presentation witness. Its exact
formula is

```text
(a.fullRecognitionIdempotenceIndex W).chart x =
  W.chart ((a.fullRecognitionIdempotenceAlgebraEquiv W).spectrumHomeomorph x).
```

The spectrum homeomorphism has the contravariant direction from the new
earlier-atlas presentation to the original iterated parent.

Finally, `fullRecognitionAtlas_chartFamily_idempotent` proves

```text
range (fun i => range (a.fullRecognitionAtlas.fullRecognitionAtlas.chart i))
  = range (fun i => range (a.fullRecognitionAtlas.chart i)).
```

For the forward inclusion, the explicitly constructed idempotence
index has the identical chart range. For the reverse inclusion, each
original chart of the first full recognition atlas is its own actual
whole local domain and is recognized in the next full atlas by the
already constructed original-local-domain embedding. This is equality
of literal families of subsets of the same ambient space.

The coefficient-field, ambient-space and original-index universes remain
independent. The complete ultrametric field may have trivial valuation.
There is no ambient Hausdorff, reducedness, nonzero-algebra or
nonempty-cover premise; empty finite covers and spectra remain allowed.
Every represented-domain property retains its full quantification over
presented affinoid test algebras.

The proof constructs the required finite overlaps inside a common actual
affinoid parent. It does not assume the general special-intersection
lemma, closed-ideal effectiveness or a new Kiehl-descent input.
It establishes literal chart-family idempotence with the stated actual
algebra and chart comparisons. Arbitrary equivalent-net invariance,
maximal-atlas uniqueness, a natural comparison of all final algebra
restrictions, unrestricted analytic morphism identification and the
analytic étale and equivariant sites remain later obligations.
