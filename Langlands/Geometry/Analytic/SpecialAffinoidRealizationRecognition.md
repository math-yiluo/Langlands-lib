# Recognition from an actual finite affinoid realization

Author: Worker 36.

This module constructs the three recognition conditions for a literal
special subset from an actual finite affinoid realization of one of its
defining covers. It constructs bounded algebra equivalences, proves
bijectivity of the existing canonical spectrum map, and transports the
full represented-domain universal properties of the unchanged component
algebras to the chart constructed from the special-subset section algebra.

The original source is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), the finite Banach equalizer following Lemma 1.2.12,
printed p.20 / PDF p.17, and the canonical map, recognition conditions and
Proposition 1.2.13(ii), printed p.21 / PDF p.18. Registered source
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Both original pages were read for this unit. No source-specific errata
file was found in the available project and Library locations.

This is a derived recognition-transfer construction, rather than the
source's general maximal-atlas theorem. Its proof combines the published
finite-realization recovery construction with the published comparison
of special-subset defining covers and bounded transport of full domains.

Fix an actual indexed affinoid atlas `a`, a literal special subset `W`,
a finite original-chart family `d`, and an equality `hd : d.locus = W.val`.
An input `c : d.AffinoidRealization` supplies an actual finite closed
weighted Tate presentation `A`, an embedded continuous chart with range
exactly `d.locus`, bounded maps from `A` to the original component
algebras, their chart formulas and full represented-domain universal
properties, and compatibility of the entire bounded overlap maps.
Neither an equivalence with the section algebra nor any recognition
conclusion is supplied. The final recognition theorem also requires
`hspecial : d.IsSpecialCover`; this includes the actual overlap tensor
admissibility conditions of the existing special-cover definition.

`range_comap_componentRestriction` first proves an identity that applies
to any defining cover of `W` whenever intrinsic affinoidness and
bijectivity of its canonical map are available. The range of the comap
of the canonical component restriction is exactly the inverse image of
the original component's ambient range under `W.chart`. In one direction,
the existing component chart formula gives a range witness. In the other,
an original component spectrum point gives a preimage, and injectivity
of the constructed chart identifies its comap with the given point.
This lemma does not assume full representation of the component map.

`realizationSectionEquiv` constructs a full bounded equivalence
`A ≃ W.SectionAlgebra`. It composes the recovered equivalence
`A ≃ d.SectionAlgebra` with the inverse of the actual comparison
`W.SectionAlgebra ≃ d.SectionAlgebra`. The section equalizers retain their
original norms and all algebra elements.
`isAffinoid_of_affinoidRealization` transports the proved intrinsic
affinoidness of `d.SectionAlgebra` along that inverse comparison.
Intrinsic affinoidness means an actual admissible epimorphism from a
finite positive-polyradius Tate algebra, and constructs a closed-kernel
presentation of the unchanged special-subset section algebra.

`spectrumMap_eq_affinoidRealization` identifies the exact existing
`W.spectrumMap` with the composite of the literal-subset homeomorphism,
`d.spectrumMap`, and the comparison's spectrum homeomorphism. Its proof
uses the existing comparison formula on the same ambient point.
`spectrumMap_bijective_of_affinoidRealization` then composes the proved
bijectivity of the finite-realization canonical map with the two
homeomorphisms. It does not substitute an unrelated bijection for the
canonical map used by recognition.

`realizationPresentationEquiv` constructs a bounded equivalence from
`A` to the finite presentation just obtained from intrinsic affinoidness.
It composes `realizationSectionEquiv` with the inverse of the constructed
presentation-to-sections bounded equivalence.
`componentRestriction_affinoidRealization` identifies each canonical
component map with the original bounded restriction from `A` composed
with the inverse of this new equivalence. This is equality of entire
bounded algebra maps: the proof evaluates the full projection-recovery
identity from finite full-domain descent on an arbitrary algebra element.
No faithfulness of spectrum points is used.

`componentRestriction_represents_of_affinoidRealization` transports the
input component's full representation along this bounded equivalence.
The quotient algebra remains the original component algebra, and the
universal property still tests every presented positive-polyradius
affinoid algebra. The transported representation identifies its locus
with the comap range of the transported map. The proved bounded-map
identity and `range_comap_componentRestriction` identify that range with
the required literal relative component locus in the constructed chart.
Thus the locus identification requires no assumed global comparison
between the two charts.

`isRecognized_of_affinoidRealization` supplies the constructed intrinsic
affinoidness and canonical-map bijectivity, the given special defining
cover, and the proved full component representations as witnesses of
`W.IsRecognized`. These are exactly its three recognition conditions.

The coefficient field is complete and ultrametric, including trivially
valued fields. The field, ambient-space and chart-index universes remain
independent. The ambient space need not be Hausdorff. No reducedness,
nonempty-cover or nonzero-algebra hypothesis is added; all cases remain
subject to the stated realization and covering conditions.

The result is conditional on the explicit actual realization and special
cover. It does not construct these data for every domain in a recognized
chart, prove tensor admissibility of an arbitrary finite cover, establish
maximal affinoid closure or idempotence, or construct the analytic étale
or equivariant sites. The general special-intersection statement and
closed-ideal effectiveness are not assumed. Those geometric existence
and application obligations remain separate from this proved transfer.
