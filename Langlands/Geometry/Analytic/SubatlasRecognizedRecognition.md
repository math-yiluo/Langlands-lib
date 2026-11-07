# Recognition of arbitrary original recognized subsets in a selected atlas

Author: Worker 36.

Every recognized subset of an original local-domain saturation has a
constructed recognized presentation in the saturation of a locally
refining selected atlas. The construction keeps its literal ambient locus
and produces a bounded algebra equivalence recovering its original chart.

## Source and provenance

This is derived infrastructure for Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), Proposition 1.2.13(i)–(ii),
printed p.21 / PDF p.18. The registered source is
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The original page was read in this development; no source-specific errata
file was available in the Library notes.

Part (i) compares completed domain families under passage to a subnet;
part (ii) constructs canonical bounded restrictions in the extended
atlas. This module supplies the original-to-selected recognition
construction for arbitrary original recognized subsets under the explicit
local refinement hypothesis. Its overlap representatives and section
algebra comparisons are internal implementation choices. The argument
reuses the constructed finite realization from
`SubatlasRecognizedAffinoidRealization`, the full-domain and completed-tensor
universal properties, and the generic finite-realization recognition
criterion. Recognition or a bounded comparison with the output is not an
input.

Let `a` be the original indexed affinoid atlas, let `P` be a selection
with `hP : a.IsLocallyRefiningSelection P`, and write
`b = a.subatlas P hP`. The remaining input is an arbitrary
`V : a.saturatedAtlas.RecognizedSubset`.

## Actual overlap quotients and their entire bounded maps

Write `d = a.subatlasRecognitionGluing hP V`. Its finite components `E`
and `F` are canonical full domains over exactly `V.algebra`. Their
intersection `E.inter F` has the actual affinoid pushout quotient algebra.
The preceding construction extends its relative domain through the
selected local representative of the first component, obtaining an actual
`b`-local domain with precisely the ambient intersection locus.

`subatlasRecognitionOverlapEquiv` applies `b.localDomainSaturatedEquiv`
to that local domain. It constructs a bounded algebra equivalence from the
actual pushout quotient to the algebra chosen by `b.saturatedAtlas` for
the overlap locus. Both bounded inverse maps are retained.

`subatlasRecognitionGluing_leftRestriction` proves that the stored left
restriction is the actual pushout left map followed by this equivalence.
The inverse equal-locus comparison inclusion, followed by the relative
domain's extension inclusion, is an actual local-domain inclusion with the
same endpoints as the stored saturated inclusion. The proved uniqueness
of such inclusions identifies them. Taking their stored bounded
restrictions gives equality of entire algebra maps.

`subatlasRecognitionGluing_rightRestriction` proves the corresponding
right-map formula. It uses the full represented-domain universal property
of `F` to cancel precomposition with `F.baseMap`. The constructed finite
realization's compatibility, the proved left-map formula and the actual
pushout structural equation identify those precompositions on every
algebra element. This step retains nilpotent information.

`subatlasRecognitionGluing_overlapTensorMap` identifies the genuine
completed-tensor overlap map with the actual pushout tensor quotient map
followed by the overlap equivalence. Completed-tensor homomorphism
uniqueness reduces the equation to its two entire structural legs; the
preceding restriction formulas and the pushout tensor-leg equations prove
them.

## Admissibility, specialness and recognition

`subatlasRecognitionGluing_tensor_isAdmissibleEpi` proves admissibility
of every overlap tensor map. The overlap equivalence has a bounded
section given by its actual inverse, hence is an admissible epimorphism.
Composition with the actual pushout tensor quotient, already an admissible
epimorphism, supplies surjectivity and the uniform positive quotient-norm
bound.

`subatlasRecognitionGluing_isSpecialCover` combines these results with
the Hausdorff topology on `d.locus` transported from the unchanged parent
Banach spectrum through the constructed realization homeomorphism. No
global Hausdorff hypothesis on the ambient space is needed.

`subatlasRecognitionSpecialSubset` packages `V.locus` with this actual
finite special cover and its proved literal union equation.
`subatlasRecognizedSubset` applies
`SpecialSubset.isRecognized_of_affinoidRealization` to the constructed
cover and realization. That criterion proves intrinsic affinoidness of
the canonical section algebra, bijectivity of its canonical spectrum map,
and the full represented-domain property of its component restrictions.
Intrinsic affinoidness includes a finite positive-radius Tate
presentation. The theorem `subatlasRecognizedSubset_locus` identifies
the result's locus with `V.locus` by definitional equality.

## Algebra and ambient chart recovery

`subatlasRecognizedSubsetEquiv` is an actual bounded algebra equivalence
from `V.algebra` to the constructed selected recognized algebra. It
composes the finite realization's equivalence with the canonical section
algebra and the inverse of the selected recognized presentation's
canonical equivalence. These maps are constructed by the generic section
algebra comparison; an output algebra isomorphism is not assumed.

For every point `x` of the selected recognized spectrum,
`subatlasRecognizedSubset_chart` proves

```text
selectedRecognized.chart x =
  V.chart (subatlasRecognizedSubsetEquiv.spectrumHomeomorph x).
```

This is the generic chart-recovery theorem applied to the constructed
special cover and realization, whose parent algebra and chart are exactly
those of `V`.

## Hypotheses and remaining scope

The field is complete and ultrametric, with trivial valuations allowed.
The field, ambient space and original atlas indices have independent
universes. There is no added global Hausdorffness, reducedness,
nonzero-algebra or nonempty-cover premise.

This unit constructs recognition and algebra/chart recovery in the
original-to-selected direction. Recovery of all bounded restrictions,
functorial naturality, reverse recognition and the resulting category
comparison remain subsequent work. Arbitrary equivalent-net invariance,
maximal-atlas uniqueness, the analytic morphism comparison, etale and
equivariant sites, and the Harris specialization remain obligations of
the host task.
