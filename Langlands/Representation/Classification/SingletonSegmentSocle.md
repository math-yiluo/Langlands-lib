# Actual socles for one-term segments

Author: Worker 494.

This internal module converts a supplied actual cuspidal-product embedding into
actual segment-socle product data. It preserves the total rank, factor order,
each actual representation and the given full-product embedding. The segments
have length one. The conclusion asserts no precedence ordering or uniqueness
of the full product's irreducible subobject. In particular, it is a supporting
unit for independent socle exhaustion, not a proof of exhaustion.

## One-term induction and exact rank transport

`T.singletonSegment ρ` has base `ρ` and length one. Its degree is `1 * ρ.rank`,
and `singletonSegment_degree` gives the exact equality with `ρ.rank`.

`T.castRank h A` transports the bundled smooth representation `A` along a rank
equality `h : r = s`, using ordinary equality elimination. Its associated
`castRankEquiv` identifies this representation with `A.representation` pulled
back along the inverse of `GeneralLinear.reindex (finCongr h)`. The proof
eliminates `h`, uses the identity linear equivalence, and compares matrix
entries to show that the resulting reindexing is the identity. The lemma
`isIrreducible_castRank` similarly eliminates the equality. These constructions
work with independent field and carrier universes.

`T.singletonSegmentInducedEquiv hr A` is an actual representation equivalence
from `T.segmentInduced A 1 hr` to `T.castRank (Nat.one_mul r).symm A`.
The proof applies the published
`T.singleBlockNormalizedProductEquiv` to the actual uniform one-block shape.
This is evaluation for normalized induction from the whole group followed by
the actual singleton tensor equivalence; its explicit half-modulus is one.
The sole factor has twist exponent zero. `realPowerCharacter_zero` and
`twist_one` identify its action with `A.representation`. Composing this
identification with `castRankEquiv` retains exactly the published matrix rank
transport. No substitute induction or tensor construction is introduced.

## The actual strong segment socle

For `ρ : CuspidalDatum.{max uF uV,uF} T` and an actual saturated supercuspidal
representative `A` satisfying `ρ.IsRepresentedBy A`,
`singletonSegment_isSegmentSocle` proves

```text
T.IsSegmentSocle (T.singletonSegment ρ)
  (T.castRank (T.singletonSegment_degree ρ).symm A.obj).
```

Irreducibility of `A` is part of its supercuspidal object. Exact transport
preserves it, and `Weil.IsomorphismInvariance.irreducible_iff` transfers it to the
one-term induced representation along the constructed equivalence. The inverse
equivalence supplies an injective intertwiner into that induced representation.
The published
`Classification.IsIrreducibleSubrepresentation.isIrreducibleSocle_of_irreducible`
upgrades this to the strong socle relation: every irreducible embedding into an
irreducible ambient representation is onto, so all such images are the whole
ambient space. Thus this conclusion includes subobject uniqueness, not just an
irreducible constituent or an isomorphism class. Saturation ensures all carriers
in this strong-socle relation have the same universe, while `uF` and `uV` remain
independent.

## Products and supplied embeddings

`normalizedProductRankCastIso` treats a finite family of positive ranks with
pointwise exact equalities to another family, both summing to the same total.
It constructs an isomorphism from induction of the transported factors to
induction of the original factors, using the actual normalized upper product
induction functor. The proof converts the pointwise equalities to a function
equality and eliminates it. Rank casts then reduce to the identity, and the
positivity and sum witnesses agree by proof irrelevance. The resulting
isomorphism is the identity. This argument changes only the presentation of
the exact ranks; it does not permute or regroup factors.

`SegmentProductDatum.ofCuspidals T ρ h A` assigns each original factor the
one-term segment with that cuspidal base and the exactly transported actual
representation `(A i).obj`. Its degree-sum equality follows from
`singletonSegment_degree` and the given cuspidal rank sum `h`.
`ofCuspidals_hasSegmentSocles` applies the individual strong-socle result at
each index. `ofCuspidalsInducedIso` specializes `normalizedProductRankCastIso`
to give an actual isomorphism between the resulting segment product and
`T.cuspidalProductInduced ρ h A`.

`IsCuspidalSubrepresentation.exists_segmentSocleProduct` unpacks the supplied
cuspidal-product relation, constructs this datum, and composes its induced
isomorphism with the supplied injective intertwiner. Its conclusion retains
the source representation's irreducibility and gives the segment-socle
condition and genuine full-product embedding. It allows an empty index type
when the supplied relation allows one. It does not assert that arbitrary
irreducible representations have a cuspidal-product embedding; that is a
separate existence theorem.

## Provenance and independence

This is derived internal infrastructure using current Library declarations by
Lean name. No original literature is claimed as a newly formalized theorem.
The direct inputs are:

- `Induction.SingleBlock`: actual full-parabolic evaluation, singleton tensor
  evaluation and the explicit inverse matrix rank transport.
- `Classification.Segments` and its twist imports: the segment, segment induction,
  determinant-power character, trivial twist and strong-socle relations.
- `Classification.SegmentSocleProductData`: the elementary irreducible-ambient
  strong-socle lemma described above. That lemma uses only the strong-socle
  definition, simple-module nontriviality and Schur's surjectivity alternative.
- `Classification.SupercuspidalSupport`: actual cuspidal product, representatives,
  rank sum and injective intertwiner in `IsCuspidalSubrepresentation`.
- `Weil.Representation.IsomorphismInvarianceProof.irreducible_iff`: the elementary
  group-algebra module equivalence associated to a representation equivalence.

The project import graph has 97 modules. It includes
`OrderedMultisegmentHeadReduction` through `SegmentSocleProductData`, but the
only declaration used from `SegmentSocleProductData` here is its first,
elementary irreducible-ambient socle lemma. That lemma uses no declaration from
`OrderedMultisegmentHeadReduction`. Other declarations and imported proposition
definitions supply no mathematical assumption to this proof.

There is no use, directly or through the implemented proof dependencies, of
special-head exhaustion or ordered special-head existence, analytic segment
classification, quotient coverage, tempered block uniqueness, square-integrable
classification or exhaustion, or regular exhaustion. No general segment-socle
existence, local linked reduction, unlinked product commutation, or ordered
full-product strong-socle theorem is assumed proved. All existing Library
Lean/Markdown pairs are unchanged.
