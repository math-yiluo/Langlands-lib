# Actual cuspidal quotients of special-head products

Authors: Worker 357 (independent-universe construction and data bundle),
Worker 328 (the adapted support-realization construction), and Worker 627
(the adapted dependent rank-transport pattern).

`Langlands.Classification.segmentHeadProductCuspidalQuotient` constructs
`SegmentHeadProductCuspidalQuotientData T d` for every
`d : T.SegmentProductDatum.{uV,uF} n` with `d.HasSegmentHeads`.
The prime, field `F : PadicField.{uF} p`, supplied topology `T`, rank `n`,
and universes `uF` and `uV` are arbitrary. The construction does not require
irreducibility of the product. Its corollary
`segmentHeadProductCuspidalSupportIndependent` uses that extra premise to
supply the exact supercuspidal support of the induced product.

This is a supporting construction for the special-head irreducibility
criterion. It supplies neither direction of that criterion.

## The constructed data and universe distinction

The data bundle contains a finite family of cuspidal data, its rank sum,
its equality with `d.multisegment.cuspidalContent`, actual supercuspidal
representatives of that family, their class equalities, and a surjective
morphism from their normalized cuspidal product to `d.induced`.
Every occurrence in every segment is retained, including repeated segments
and repeated cuspidal members.

Segment bases, all chosen base and member representatives, and the flat
inducing factors have carrier universe `uV`. Inner segment induction,
outer induction and the flat cuspidal product have carrier universe
`max uF uV`. This matches the independent, unsaturated base universe in
`SegmentHeadProductIrreducibility`.

The published theorem `segmentHeadProductCuspidalSupport` instead takes
`d : T.SegmentProductDatum.{max uF uV,uF} n`. Its proof provides the
construction adapted here; its theorem is not an input to this module.
The adaptation applies `Parabolic.orderedProductRegrouping.{uF,uV}` to
cuspidal factors in `uV`. That theorem already gives the outer induction
at `max uF uV`, so no resizing or lift of cuspidal classes is needed.
The definition of the abstract rank-transport helper stays at `uV` as well.

## Construction

For each segment occurrence `j`, `IsSegmentHead.isSegmentQuotient` extracts
an actual representative `A j` of its base and a surjective intertwiner
from the increasing segment induction to `d.blocks j`. The construction
chooses these witnesses from the supplied head relations. It does not
apply an existence theorem for segment heads or for a reversed socle.

`normalizedProductMap_surjective` gives the surjectivity of the actual
product morphism `Q` from the nested segment inductions to `d.induced`.
It uses the actual external tensor map, whose surjectivity follows by
lifting the coordinates of pure tensors, and the published surjectivity
of smooth induction. The parabolic adapter supplies closedness of the
block parabolic, cofinal compact open subgroups, smooth pullback and the
open kernel of the positive half-modulus twist. Thus it preserves the
specified normalized product map.

The shared [SegmentProductCuspidalMembers](SegmentProductCuspidalMembers.md)
module supplies the ordered refinement in namespace
`Langlands.Classification.SegmentProductCuspidalEmbedding`. It reuses the
published implementation by Worker 1070, with the attribution to Workers 328
and 627 retained in its companion. Each segment block is refined into a
uniform shape of its segment length and positive cuspidal rank. The
flattened labels correspond consecutively to pairs of a segment index
and a member index. The family `memberFamily` takes the corresponding
`Segment.member`, and `memberRepresentatives` uses the determinant-power
twist of `A j` by that member index. Applying the same class twist to the
base representative equality proves `memberRepresentatives_represent`.

`memberInducedIso` applies the published ordered regrouping theorem to
this refinement. The flatten-size identities give the rank comparisons,
and `index_index_eq_flatten` supplies the exact equality of ambient
coordinates. The equality-elimination helper `memberRankIso` identifies
each transported factor with the precise factor in the increasing
segment induction. Functoriality through inner and outer induction then
gives an isomorphism from the flat cuspidal product to the source of `Q`.
The constructor selects this isomorphism by classical choice and composes
its forward morphism with `Q`. Both maps are surjective.

`memberFamily_content` writes an indexed multiset as a sum of singleton
multisets, reindexes by the inverse flattening equivalence, and separates
the sum over pairs into the two finite sums. The inner sums are the
segment contents and the outer sum is the multisegment content. This is
an equality of multisets, with no passage to sets or deduplication.

For the corollary, the same chosen family, representatives and surjective
morphism form a quotient witness. `SmoothRep.IsQuotient.isSubquotient`
supplies the subquotient field of `IsCuspidalConstituent`. Together with
the corollary's irreducibility premise and the content equality, this
is exactly `T.IsSupercuspidalSupport d.induced d.multisegment.cuspidalContent`.
No uniqueness theorem for cuspidal support is used.

The construction allows rank zero and the empty overall family. It never
chooses an element of an empty index type: each choice is pointwise, the
flattened family is empty, and the published tensor, induction and
regrouping results already include that case.

## Derived provenance

This is an internal composition of the current Library's actual quotient,
ordered induction, tensor and support constructions. The flat member
construction adapts `SegmentHeadProductCuspidalSupportProof`; the new data
bundle records its actual morphism before any product irreducibility
premise is imposed. The dependent rank-transport argument ultimately
adapts Worker 627's equality-elimination pattern. No tempered theorem or
hypothesis is used by that argument.

The original structural context is Zelevinsky, *Induced representations of
reductive p-adic groups II*, 1980, registered source
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The original was read at section 1.1(a,c), printed p.170 / one-based PDF
p.7 (exactness and induction in stages), section 1.5(b), printed p.171 /
PDF p.8 (the tensor-coordinate comparison), and section 1.10, printed
p.174 / PDF p.11 (multiset cuspidal support realized by a constituent).
The present data structure and construction are derived from the formal
maps; they are not attributed verbatim to any of these passages.
No applicable source-specific erratum was found in the supplied literature
filenames or project notes; the source-boundary note
`notes/henniart/gln-classification-sources.md` was also consulted.

## Dependency audit

The submitted version's transitive import inventory against supplied Library
`e3944f764d2c00d53ac87227e98601bb667f348f` has 138 project modules including
this module, and 90 external import roots. All 137 inherited project
Lean/Markdown pairs match that Library byte for byte. Relative to the
current support-realization proof closure, this replaces its root and
statement module by this construction module; the remaining imported
modules are identical.

The only inherited classification modules are `ConstituentRelations`,
`Essential`, `LanglandsData`, `SegmentCuspidalContent`, `Segments`,
`Supercuspidal`, `SupercuspidalSupport`, `SupercuspidalTwist` and `Tempered`.
They supply the actual predicates, primitive head witnesses, determinant
twists and elementary transport facts. None supplies an excluded
classification conclusion.

The direct proof routes were checked in `InducedMapSurjectivity`,
`ExternalMapSurjectivityProof`, `Induction.SurjectivityProof`,
`OrderedProductRegroupingProof`, `RefinedInductionTensorProof`,
`RefinementInductionTransitivityProof`, `Tensor.GLRefinement`, and the
flattening section of `CuspidalSupport.MinimalJacquetProof`.
The regrouping proof composes coordinate normalization, the actual tensor
regrouping equivalence, normalized induction in stages, and refined
induction's pointwise tensor comparison. Its lower infrastructure is
finite tensor algebra, compact sections, and coordinate/modulus identities.
Only finite flattening constructions are used from `MinimalJacquetProof`;
its minimal-Jacquet existence theorem is not applied.

There are no derivative, Whittaker, segment-Jacquet-comparison or
classification-exhaustion proof modules in this closure. In particular,
this construction does not use the excluded special-head Jacquet formula,
Ze80 segment derivative formulas 3.5 or 9.6, or any part of
`SegmentSocleDerivatives`. It uses no generic segment-product uniqueness,
multisegment exhaustion, ordered strong-head existence, quotient coverage,
ordered conversion, tempered uniqueness, square-integrable Langlands
classification, square-integrable exhaustion, regular exhaustion or
special-head product irreducibility conclusion. Inherited essential and
tempered definitions impose no extra hypotheses on this construction.
The derivative results and independence audits needed for the full criterion
remain separate obligations.

Integration replaces the duplicated member helpers with the identical published
implementation in the shared member module. The public quotient data and support
conclusion are unchanged, and the shared module imports only the lower
construction dependencies.

The submitted module and constructor inspection compile successfully with only
`propext`, `Classical.choice` and `Quot.sound` as axioms. Development
compilation is not independent semantic acceptance or publication.
