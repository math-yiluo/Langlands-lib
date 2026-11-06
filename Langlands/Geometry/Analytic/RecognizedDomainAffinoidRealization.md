# Actual finite affinoid realizations of recognized-chart domains

Author: Worker 36.

This module constructs an actual finite affinoid realization for every full
affinoid domain in a recognized chart over the full local-domain atlas.
Its parent algebra is the given domain algebra. The finite component
algebras are the presentations already chosen by the saturated atlas;
their bounded maps, full representations and compatibility are constructed.
Pairwise overlaps come from actual affinoid pushout quotients.

The source motivation is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), the finite Banach equalizer following Lemma 1.2.12,
printed p.20 / PDF p.17; the recognition conditions and
Proposition 1.2.13(ii)–(iii), printed p.21 / PDF p.18; and
Definition 1.3.1 and its following paragraph, printed p.23 / PDF p.20.
Registered source `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These original pages were read for this unit. No source-specific errata
file was found in the available project and Library locations.

This is a derived construction toward closure of the recognized atlas
under full affinoid domains. It instantiates the existing
`FiniteChartGluingData.AffinoidRealization` construction using actual
domains and maps. The source does not state this intermediate construction
separately. The result does not assume a realization or a section-algebra
comparison, and does not yet prove specialness of the constructed cover
or the source's entire maximal-atlas assertion.

First let `V : a.RecognizedSubset` and `D : Domain K V.algebra`.
`domainLocus_subset` records that `V.chart '' D.locus` lies in `V.locus`.
Suppose an original chart indexed by `parent` is contained in this domain
locus. The existing `V.originalDomain parent` is a full domain over
`V.algebra`, with the original chart algebra. The containment and
injectivity of `V.chart` show that its locus is contained in `D.locus`.
`domainOriginalInclusion` applies the full universal property of `D` to
construct the actual inclusion from that original domain to `D`.

`domainOriginalDomain` passes this inclusion to its relative full-domain
representation over `D.algebra`. It retains the original chart algebra
literally, as `domainOriginalDomain_algebra` states. Its structural bounded
map is the constructed inclusion restriction.
`domainOriginalDomain_baseMap_comp` recovers the entire original bounded
restriction after composition with `D.baseMap`.
`domainOriginalDomain_locus` identifies its exact relative locus as

```text
V.domainAmbientMap D ⁻¹' range (a.chart parent).
```

`domainOriginalDomain_over_ambient` identifies the actual ambient map
with the original chart, using the inclusion's structural-map equation
and the recognized chart recovery formula.
For nested original charts, `domainOriginalDomain_naturality` proves
equality of the entire bounded maps over `D.algebra`. It cancels
`D.baseMap` by the full represented-domain uniqueness theorem. The
remaining equality is the existing naturality of original restrictions,
evaluated on arbitrary algebra elements. Equality on spectrum points is
not used to deduce equality of algebra maps.

Now let `V : a.saturatedAtlas.RecognizedSubset`. The imported
`fullRecognitionDomainPiece` construction gives finitely many original
local domains whose literal loci cover `V.domainLocus D`.
`fullRecognitionDomainIndex` uses each such locus as an index of the
saturated atlas. The range and containment theorems recover the precise
piece locus and its containment in the parent domain.
`fullRecognitionDomainComponent` applies `domainOriginalDomain` to these
indices. Thus every component is a full domain over `D.algebra`, with the
unchanged chosen saturated-chart algebra. Its locus and ambient-map
theorems give the exact inverse-image formula and original chart recovery.

For two components `E` and `F`, `fullRecognitionDomainOverlap` forms the
actual full-domain intersection `E.inter F` over `D.algebra`. This uses
the affinoid pushout quotient of their actual structural bounded maps.
It regards this intersection as a relative full domain over `E.algebra`
using the left pushout leg, then extends it through the original local
domain representing the first saturated chart. Extension retains the
actual intersection quotient algebra, as
`fullRecognitionDomainOverlap_algebra` states.

`fullRecognitionDomainOverlap_locus` proves that this extended local
domain has exactly the intersection of the two chosen chart ranges.
The proof uses the relative-image formula for the actual intersection
and the established component ambient-map formula. For the reverse
inclusion it uses containment in the parent's actual chart range.
This argument requires no Hausdorff assumption on the ambient space.

`fullRecognitionDomainGluing` packages the component indices and the
literal overlap loci as finite gluing data in the saturated atlas.
Its overlaps are represented original charts of that atlas.
`fullRecognitionDomainGluing_locus` proves that their finite union is
exactly `V.domainLocus D`, using the imported finite piece coverage.

`fullRecognitionDomainAffinoidRealization` constructs every field of the
realization: the actual parent `D.algebra`, its embedded ambient chart,
the exact range equality, all bounded component maps, their full
represented-domain universal properties and their original chart formulas.
For each overlap, the two naturality equations above identify the bounded
composites with the same canonical domain restriction, proving entire-map
compatibility. No realization data or global section comparison is
supplied as an extra hypothesis.

The coefficient-field, ambient-space and original-index universes are
independent. The complete ultrametric field may have trivial valuation.
No reducedness, nonzeroness, nonempty-cover or ambient Hausdorff
hypothesis is added. All full-domain universal properties quantify over
every presented affinoid test algebra with finite positive polyradii.

The unit constructs the finite realization. It does not yet prove
admissibility of its completed-tensor overlap maps, specialness of its
finite cover, recognition of the entire domain, maximal closure,
idempotence or the unrestricted morphism-category identification.
The general special-intersection statement and closed-ideal effectiveness
are not assumed. Analytic étale and equivariant sites and the Harris tower
specialization remain later obligations.
