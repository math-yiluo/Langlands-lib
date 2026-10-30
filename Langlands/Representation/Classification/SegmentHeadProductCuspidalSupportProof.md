# Cuspidal support realization for segment heads

Authors: Worker 328 (support realization and proof); Worker 627 (adapted rank
transport pattern).

`Langlands.Classification.segmentHeadProductCuspidalSupport` proves exactly the
published proposition
`Langlands.Classification.SegmentHeadProductCuspidalSupport.{uF,uV} F T`.
Its outer parameters are precisely
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
There are no additional theorem hypotheses.

For every rank `n` and datum
`d : T.SegmentProductDatum.{max uF uV,uF} n`, the supplied segment-head
relations and irreducibility of `d.induced.representation` give
`T.IsSupercuspidalSupport d.induced d.multisegment.cuspidalContent`.
The proof supplies an actual quotient of normalized cuspidal induction,
then the subquotient required by that support relation. It preserves all
member occurrences, including equal members and repeated segments.

The two normalized-map surjectivity adapters are imported from
[InducedMapSurjectivity](../Parabolic/InducedMapSurjectivity.md).

## Primitive quotients and their normalized product

For each block index `j`, the proof applies
`IsSegmentHead.isSegmentQuotient` to the supplied head relation. It chooses an
actual supercuspidal representative `A j` of the segment base, its
representation-of-the-base equality, and a surjective intertwining map

```text
q j : segmentInduced (A j).obj (d.segments j).length → d.blocks j.
```

These choices use the existing quotient witnesses; they require no assertion
that segment heads exist.

The shared `normalizedParabolicMap_surjective` applies the published
`Induction.smoothInductionSurjectivity` to the actual block parabolic in
`GL n`. Compact open subgroups are cofinal by
`T.generalLinearCompactOpen`, and `B.isClosed_parabolic` supplies closedness.
The two inducing representations are inflated through the continuous Levi
projection and twisted by the inflated positive half-modulus character.
Their smoothness follows from smooth pullback and the open-kernel twist
lemma. The underlying intertwiner is still the given surjective map.

The shared `normalizedProductMap_surjective` then uses the published
`FiniteTensor.externalMapSurjectivity` on the family of primitive maps and
applies the parabolic adapter to their external tensor map. This is the actual
`T.normalizedProductInducedMap`, whose definition is normalized parabolic
induction of that external map. Packaging it with `SmoothRep.ofHom` gives
a surjective morphism `Q` from the nested product of increasing segment
inductions to `d.induced`.

## Actual member representatives and ordered regrouping

`memberRefinement` replaces the block belonging to each segment by its uniform
shape: one block of the segment's cuspidal rank for each member index. Let
`S` be this refinement, `B := d.shape.flatten S`, and
`e := d.shape.flattenBlockEquiv S`. A flattened label `k` corresponds to the
pair `q := e.symm k`, consisting of a segment occurrence and a member occurrence.
`memberFamily d k` is exactly `(d.segments q.1).member q.2.val`.
Its rank sum is the actual flattened shape's `sum_eq`.

`memberRepresentatives` realizes that datum by twisting `A q.1` by
`T.determinantPowerCharacter` with exponent `(q.2.val : ℝ)`.
`SupercuspidalRep.twist` constructs the actual supercuspidal object, using the
open character kernel and containment of the determinant kernel.
`memberRepresentatives_represent` applies the same class twist to the chosen
base-class equality. Thus the representatives realize the exact imported
members rather than merely some cuspidal data of the same ranks.

`memberInducedIso` specializes the published, closed theorem
`Parabolic.orderedProductRegrouping` with:

- the original fine shape `B` and outer shape `d.shape`;
- the uniform inner shapes `S`, label equivalence `e`, and the exact rank
  equalities from `flatten_size_flattenBlockEquiv`;
- the consecutive ambient-coordinate equality
  `d.shape.index_index_eq_flatten S`;
- the actual member representatives as the fine factor family.

For each inner block, `memberRankIso` eliminates the equality
`e.symm (e ⟨j,k⟩) = ⟨j,k⟩`, including its dependent rank transport.
`Pi.isoMk` and functoriality of normalized induction identify the transported
inner family with the exact `T.segmentFactor` family defining the increasing
segment induction. Applying the outer product functor to these inner
isomorphisms and composing with ordered regrouping gives an actual isomorphism
from `T.cuspidalProductInduced memberFamily memberFamily_sum memberRepresentatives`
to the source of `Q`.

## Multiplicities and the support witness

`ofFn_multiset_eq_sum` expresses the multiset of a finite indexed family as the
sum of its singleton multisets. `memberFamily_content` applies it, reindexes
through `e.symm`, and uses `Fintype.sum_sigma'` to obtain a sum over segment
indices and their member indices. The inner sums are exactly the imported
segment contents; the outer sum is exactly
`d.multisegment.cuspidalContent`. No deduplication or arbitrary permutation of
the member order is used.

The final proof supplies the flattened length, member family, exact multiset
equality, rank-sum equality, actual supercuspidal representatives, and their
representation equalities. The irreducibility field is the statement's given
premise. Composing the regrouping isomorphism's forward morphism with `Q`
gives a surjective morphism from the actual cuspidal product to `d.induced`.
`SmoothRep.IsQuotient.isSubquotient` turns this quotient into the required
subquotient. These are precisely the fields of the imported support relation.

The field and carrier universes remain independent. All cuspidal data and
objects here use the saturated carrier universe `max uF uV`, which also
contains the induced carriers. There is no positive total-rank assumption or
nonempty-family assumption: empty sums, finite tensors, the published
regrouping theorem, and the quotient argument retain the rank-zero case.

## Provenance and dependency independence

This is an internal derivation from primitive head quotients and published
lower constructions. The rank-transport helper and its use in the regrouping
specialization adapt Worker 627's generic equality-elimination pattern in
`TemperedSpecialSegmentRefinementAssembly`. That module is not imported, and
none of its classification hypotheses or conclusions is applied.

The original source context is A. V. Zelevinsky, *Induced representations of
reductive p-adic groups II. On irreducible representations of GL(n)*,
Ann. Sci. ENS (4) 13 (1980), pp.165–210, registered as
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The original PDF was read at §1.1(a,c), printed p.170/PDF p.7
(exactness and stages), §1.5(b), printed p.171/PDF p.8 (tensor coordinates),
and §1.10, printed p.174/PDF p.11 (support as a multiset realized by an
irreducible constituent). Section 9.10, printed p.201/PDF p.38, is only
motivation from the narrower unlinked special-representation setting.
The present statement is derived and is not attributed verbatim to §9.10.
No classification assertion from that passage enters the proof.
No source-specific errata note was found in the audited Library; the published
`notes/henniart/gln-classification-sources.md` was consulted for its source
boundary. The implemented argument uses actual Library maps and isomorphisms,
with the Library's upper parabolic, right translation, and positive
half-modulus convention.

The project import closure was audited against Library commit
`0919e099773f27747229067f0eba50e584ada6b8`. All 135 inherited project
Lean/Markdown pairs are unchanged. The mathematical dependency routes are:

- External-map surjectivity lifts pure tensor coordinates and extends by
  tensor induction. Smooth-induction surjectivity lifts compact fixed vectors
  by averaging and assembles double-coset sections. The GL adapter supplies
  topology, compact open subgroups, and closed parabolics.
- Ordered regrouping composes actual coordinate normalization, the GL tensor
  regrouping equivalence, intrinsic normalized induction in stages, and
  refined induction's tensor comparison. The last comparison uses the
  finite-product pointwise map, proved bijective by compact double-coset
  sections and linear algebra. Coordinate normalization uses the actual
  conjugation and modulus identities; stages uses evaluation at the inner
  identity and its explicit inverse.
- The flattening declarations imported from `MinimalJacquetProof` are finite
  ordered block constructions and coordinate equalities. Its minimal-Jacquet
  existence theorem is not applied. Supercuspidal determinant twists use the
  unchanged unipotent coinvariant quotients, twist invariance of
  irreducibility, and smooth admissibility under open-kernel twists.

These routes use no generic segment-product uniqueness, multisegment
exhaustion, ordered strong-head existence, quotient coverage, ordered
conversion, tempered uniqueness, square-integrable Langlands classification,
square-integrable exhaustion, regular exhaustion, supercuspidal-support
uniqueness, or all-rank cuspidal-induction association theorem. Inherited
tempered and essential-representation definitions in the statement's closure
provide no classification proof input. Product irreducibility remains the
explicit premise; no nonlinkage, precedence order, genericity, finite length,
admissibility of the product, or support uniqueness is added.
