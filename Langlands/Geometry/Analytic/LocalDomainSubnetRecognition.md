# Recognition invariance for arbitrary local-domain subnets

For any literal net of local affinoid domains of an actual atlas, this
module constructs the selected atlas and proves that its full recognized
family is the original one. It constructs an equivalence of the recognized
inclusion categories and natural isomorphisms of their actual bounded
affinoid diagrams in both directions.

## Source and provenance

The original is Vladimir G. Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), registered as
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant passages are the net definition in §1.1, printed pp.13–14 /
PDF pp.10–11; Definition 1.2.3, printed p.16 / PDF p.13; Definitions 1.2.7
and 1.2.9, printed pp.18–19 / PDF pp.15–16; the local-domain subnet
convention, printed p.20 / PDF p.17; and Proposition 1.2.13, printed p.21 /
PDF p.18. The bar and hat notation on PDF pp.17–18 was checked against
rendered original pages.

The source allows a subnet to be any net contained in the local-domain
enlargement of the original net. `IsLocalDomainSubnet` implements this
condition directly. In particular, it permits domains beyond the original
chart family. Proposition 1.2.13(i) gives equality of the recognized
families; parts (ii) and (iii) supply the surrounding extension and
idempotence statements.

The implementation is derived from the existing local-domain atlas,
canonical restrictions from recognized presentations, general coherent
strong quasi-isomorphism comparison, and full-recognition idempotence.
The category equivalence and bounded diagram comparisons spell out
additional structure implementing the source's invariance. They are not
assumed as part of the input or attributed to a verbatim source formula.

## Input and actual selected atlas

Let `K` be a complete normed field with ultrametric distance and let `A` be
an `AffinoidAtlasPresentation.{u,v,w} K`. Its chart algebras are actual
finite positive-polyradius Tate quotients by closed ideals. The atlas has
embedding spectrum charts, local Hausdorffness, a chart net, and full
bounded restriction universal properties.

`IndexedAffinoidAtlas.IsLocalDomainSubnet σ` is the conjunction that `σ`
is a net on the unchanged ambient space and that every member lies in
`A.atlas.localDomainFamily`. The latter family consists of the literal
ambient loci of actual full affinoid domains in individual original
charts. The condition contains no recognition, algebra comparison or
inverse data.

`localDomainSubnet_selectedChartFamily` proves that selecting precisely
those indices of `saturatedAtlas` whose underlying subsets lie in `σ`
recovers `σ` literally. `IsLocalDomainSubnet.isNetSelection` transfers the
supplied net law to this selection.

`localDomainSubnetPresentation` then applies `netSubpresentation` to
`A.saturatedPresentation`. Its index type is the subtype of
`A.atlas.localDomainFamily` consisting of members in `σ`, in universe `v`.
It retains `A.space` and its topology and has index universe `v`, with no
equality imposed between the original universes `v` and `w`. Its algebra
at `S` is the algebra of `saturatedRepresentative S.val`; its chart is
`saturatedChart S.val`. Its bounded restrictions and their full
universal properties are those of the constructed local-domain atlas.
The chart-family lemma proves that the resulting chart family is exactly
`σ`. These are the canonical inherited presentations, rather than an
arbitrary second assignment of algebras to the same subsets.

## Constructed strong quasi-isomorphism

`localDomainToFullRecognition` is a strong map from the actual
local-domain presentation to `A.fullRecognitionPresentation`. Its
ambient map is the identity. For every local-domain index `S`, a target
exists because that chart is recognized by
`originalRecognitionIndex`. For every admissible target `V`, the
pullback is the constructed bounded map `V.originalRestriction S`.
Thus the map includes all admissible pairs, not only a chosen target
for each source chart.

Chart compatibility is `chart_originalRestriction`. Full bounded
restriction compatibility combines `originalRestriction_naturality`
with `originalRestriction_comp_restriction`. These are identities of
entire algebra maps. No faithfulness of spectrum points is used.

`localDomainToFullRecognition_isQuasiIso` uses the identity
homeomorphism and `originalRestriction_represents` at every admissible
pair. The required relative domain is identified using
`range_comap_originalRestriction`. The representation law retains
closedness, the exact spectrum image, and unique bounded factorization
against all presented-affinoid coefficient tests.

`localDomainToFullRecognition_hasCoherentPullbacks` follows from the
proved full-domain closure of the constructed local-domain source
atlas. It is therefore an output, not an extra closure or coherence
hypothesis on the original atlas or the selected net.

`localDomainSubnetToFullRecognition` restricts this strong map to the
selected source indices. The unit's quasi-isomorphism and coherence
lemmas inherit the complete laws from the map just constructed.
All target indices remain available.

## Recognition equivalence and literal family equality

`localDomainSubnetRecognitionEquivalence` first applies
`generalRecognizedImageEquivalence` to this coherent strong
quasi-isomorphism. This compares recognition of the selected atlas
with recognition of `A.fullRecognitionPresentation`. Composing with
`A.atlas.fullRecognitionIdempotenceEquivalence` compares directly
with `A.atlas.saturatedAtlas.RecognizedSubset`.

The forward functor preserves the literal locus because its image
formula is the image under the identity map and idempotence preserves
the locus. The reverse uses the full-recognition iteration index,
whose locus is the original locus, and the general reverse preimage
formula. The two named locus lemmas record these facts.

`localDomainSubnet_recognizedAffinoidFamily` proves equality as sets of
subsets of `A.space`. For each recognized object on either side, the
constructed forward or reverse functor supplies an object on the other
side with the same literal locus. This proves both inclusions of the
entire recognized families.

## Actual bounded diagrams

`localDomainSubnetRecognitionAffinoidNatIso` composes the general forward
bounded comparison with the full-recognition idempotence comparison,
using functor associativity and whiskering. Its type identifies the
original recognized affinoid diagram pulled back along the equivalence
with the selected recognized diagram.

`localDomainSubnetReverseRecognitionAffinoidNatIso` obtains the reverse
comparison by whiskering the inverse forward comparison with the inverse
functor, reassociating, and applying the actual equivalence counit.
The diagram `RecognizedSubset.toAffinoidSpace` takes values in the
opposite category of actual presented affinoid algebras and complete
bounded algebra maps. Both natural isomorphisms therefore retain
mutually inverse bounded maps and naturality for the entire restriction
maps. They assert isomorphisms of chosen presentations, not equality
of those algebras.

## Remaining scope

There is no original full-domain closure, local refinement, directedness,
upper cofinality, nontrivial valuation, reducedness, nonemptiness or
global Hausdorffness premise. Local Hausdorffness is part of the original
atlas data.

This unit handles every literal net in the original local-domain
enlargement, with the constructed inherited presentations. A direct
strong isomorphism between the selected and original full-recognition
presentations, comparisons for arbitrary equivalent nets or arbitrary
alternative algebra assignments, maximal-atlas uniqueness and
unrestricted analytic morphism identification remain further work.
The analytic étale and quasi-étale sites and Harris specializations
remain obligations of the larger task.
