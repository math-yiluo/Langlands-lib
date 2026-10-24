# A conditional reduction of tempered block uniqueness

Author: Worker 346.

## Scope and provenance

This module supplies an internal datum constructor and a proved conditional
reduction. It does not prove the unconditional proposition
`Langlands.Classification.TemperedBlockUniqueness`.
Its analytic classification, segment nonlinkage, and product uniqueness inputs
remain explicit hypotheses of
`Langlands.Classification.temperedBlockUniqueness_of_segment_inputs`.

The construction and reduction are derived directly from the existing Library
definitions and proved transport and uniqueness lemmas. No external source is
claimed for a new classification theorem here. The meanings and original-source
provenance of the imported propositions remain in
[TemperedBlockStatement.md](TemperedBlockStatement.md),
[SegmentSquareIntegrabilityStatement.md](SegmentSquareIntegrabilityStatement.md),
and [SegmentGenericStatement.md](SegmentGenericStatement.md).
Importing their proposition definitions supplies no proofs of them.

## Datum constructor

The namespace `Langlands.Classification.TemperedBlockUniquenessReduction`
contains the public definition `segmentProductOfPresentations`. Given a
`BlockShape n`, an actual smooth representation `σ i` of each block, a segment
`Δ i` for each index, and equalities `h i : (Δ i).degree = B.size i`, it produces
a `SegmentProductDatum n`. It retains the ordered segment family, transports
`σ i` along `(h i).symm`, and obtains the total-degree equality by summing the
given equalities and using `B.sum_eq`. The constructor itself requires no
segment-head or analytic assumptions.

The private lemma `datum_induced` identifies this datum's actual induced
representation with `(T.normalizedProductInductionFunctor B).obj σ`.
The proof destructs the block shape and uses function extensionality on the
degree equalities; equality elimination reduces the isomorphism to the identity.
Thus this step changes only rank presentations, not the order of induction.

The field and representation universes `uF` and `uV` are independent.
Representations and segment bases use the specified saturated carrier universe
`max uF uV`, with the topology supplied by `T`. No resizing is used.

## Conditional theorem and its inputs

For any prime `p`, field `F : PadicField.{uF} p`, and `T : F.TopologicalData`,
the theorem takes the following three hypotheses:

1. `SegmentEssentialSquareIntegrableClassification.{uF,uV} F T`: every
   irreducible positive-rank representation is analytically essentially
   square-integrable exactly when it is a strong segment head after rank
   transport.
2. `GenericSegmentProductUniqueness.{uF,uV} F T`: two products of supplied
   strong segment heads with pairwise unlinked segment multisets are actually
   isomorphic exactly when those multisets agree.
3. For arbitrary segments `Δ`, `Δ'` and actual representations `π`, `π'` at
   their respective degrees, strong-head witnesses and analytic
   square-integrability of both representations imply `¬ Δ.IsLinked Δ'`.
   This hypothesis is written explicitly in the theorem's type.

The conclusion is the unchanged `TemperedBlockUniqueness.{uF,uV} F T`.
The full hypotheses in items 1 and 2 are retained even though the reduction
uses only the existence direction of item 1. Unitarizability remains in the
target's block assumptions; the reduction needs only their irreducibility and
square-integrability once its three segment hypotheses are given.

## Implemented proof

In the forward implication, apply the first hypothesis separately to every
block of both products. Analytic square-integrability implies essential
square-integrability by the published
`IsSquareIntegrable.isEssentiallySquareIntegrable` lemma. Choose segment
presentations and construct both product data. Transport square-integrability
along the rank equalities and use the third hypothesis to prove that each
multisegment is unlinked. The private `datum_unlinked` lemma expresses this
blockwise argument as multiset membership.

Compose the given product isomorphism with the two `datum_induced`
isomorphisms. The second hypothesis then gives equality of segment multisets.
The private lemma `ofFn_matching` converts this equality to a permutation of
lists, uses `List.Perm.idxBij` and its inverse, and transports the index sets
along the lengths of `List.ofFn`. This produces a bijection of block indices
matching equal segments, retaining all repeated occurrences. Segment equality
gives equality of block ranks. The published
`IsSegmentHead.nonempty_iso_segmentHead` identifies each supplied head with
the canonical head of its segment, so composition yields the required actual
block isomorphisms after rank transport.

In the reverse implication, choose segment presentations only for the first
family. Reindex this family of segments along the given block bijection.
Transport its head witnesses to the second family using the given block
isomorphisms. The private `segmentHead_of_iso` composes the strong quotient
map with a representation equivalence; irreducibility and surjectivity
transport across that equivalence, and injectivity preserves the kernel
condition. The helpers `cast_iso` and `segmentHead_eq_transport` account for
the dependent rank and segment equalities by equality elimination.

The private `ofFn_eq_of_matching` uses finite cardinality equality and
`Equiv.Perm.ofFn_comp_perm` to obtain equality of the two segment multisets.
The third hypothesis establishes nonlinkage for the first family, and multiset
equality transports it to the second. Apply the reverse direction of the
second hypothesis to obtain an actual isomorphism of segment products, then
compose with the datum identifications to recover the original products.
This proves the ordering-independence implication conditionally, without
assuming injectivity of segment parameters or replacing isomorphisms with
Grothendieck-group identities.

Finally, the exported theorem eliminates rank zero using the target's positive
rank assumption and applies the two implication lemmas at successor ranks.
Proving the three segment inputs remains necessary for the unconditional
tempered block uniqueness theorem.
