# Unordered uniqueness of square-integrable tempered blocks

Author: Worker 346.

`Langlands.Classification.temperedBlockUniqueness` proves the unchanged Library
proposition `Langlands.Classification.TemperedBlockUniqueness.{uF,uV} F T`
from [TemperedBlockStatement](TemperedBlockStatement.md).

For every positive rank and two block shapes, suppose every supplied block is
an actual irreducible smooth representation, analytically square-integrable
and unitarizable. Their normalized products are actually isomorphic if and
only if a bijection of their block indices matches equal ranks and actual
block isomorphisms after the specified rank transports. Repeated isomorphic
blocks retain their multiplicities. The reverse implication includes
independence of the block ordering.

The theorem has only the parameters
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The universes `uF` and `uV` remain independent; all block carriers use
`Type (max uF uV)`. The topology, analytic square-integrability,
unitarizability, upper-parabolic normalization and actual categorical
isomorphisms have exactly the meanings of the target statement.

## Implemented proof

The proof applies the published
`temperedBlockUniqueness_of_segment_inputs` from
[TemperedBlockUniquenessReduction](TemperedBlockUniquenessReduction.md).
Its three hypotheses are discharged by the following published theorems:

1. `segmentEssentialSquareIntegrableClassification` from
   [SegmentEssentialSquareIntegrableClassificationProof](SegmentEssentialSquareIntegrableClassificationProof.md)
   identifies actual irreducible analytically essentially square-integrable
   representations with strong segment heads, after rank transport.
2. `genericSegmentProductUniqueness` from
   [GenericSegmentProductUniquenessProof](GenericSegmentProductUniquenessProof.md)
   identifies actual products of supplied strong heads for unlinked segments
   exactly by equality of their segment multisets.
3. `squareIntegrableSegmentNonlinkage` from
   [SquareIntegrableSegmentNonlinkageProof](SquareIntegrableSegmentNonlinkageProof.md)
   proves that two segments with analytically square-integrable strong heads
   are unlinked, including when their degrees differ or they coincide.

All three inputs are instantiated at the same independent universes `uF,uV`.
The last proposition unfolds to the reduction's explicit nonlinkage premise.
No premise of the reduction remains a hypothesis of the final theorem.

In the reduction's forward direction, square-integrability gives essential
square-integrability, so the first input supplies a segment presentation of
each original block. The reduction constructs product data using those same
blocks transported to the segment degrees. Its datum isomorphisms identify
these products with the original normalized products. The third input gives
nonlinkage within each family. Applying the forward direction of the second
input to the transported product isomorphism equates the segment multisets.
A finite occurrence bijection matches the two segment families. Equal
segments give equal ranks; strong-head uniqueness gives actual
isomorphisms of the corresponding original blocks after rank transport.

In the reverse direction, choose segment presentations of the first block
family and reindex them by the supplied bijection. The given block
isomorphisms transport the strong-head witnesses to the second family.
Nonlinkage for the first multiset follows from the third input and transfers
to the second by multiset equality. The reverse direction of the second
input gives an actual product isomorphism. Composing with the datum
isomorphisms yields the required isomorphism of the original products.
This argument retains repeated occurrences and does not impose an ordering
on either block family.

## Provenance and independence

This module is an internal assembly of the four imported published modules.
It introduces no new representation construction or classification
assumption. The implemented reduction and its rank transports are explained
in its paired Markdown; the three input proofs explain their analytic,
support, scalar-character and finite combinatorial arguments.

The original-source provenance of the target is recorded in
[TemperedBlockStatement](TemperedBlockStatement.md): Kudla 1994,
Proposition 1.2.3, printed pp.369–370, Theorem 1.2.5(b),(d), pp.370–371,
and the nonlinkage observation following Proposition 2.2.1, p.373;
Rodier 1982, Theorem 3(b) and Propositions 11–13, pp.211–212, give
parallel statements. This closing proof uses the actual published Lean
inputs above; the source statements and proposition definitions supply no
additional proof premise.

Neither this assembly nor the reused proof routes uses
`SquareIntegrableLanglandsClassification` or its downstream proof.
The analytic converse is supplied by the first input's Jacquet-word,
minimal-run and analytic-cone proof. Product uniqueness uses actual
cuspidal-support reconstruction and detected-constituent equivalences.
Nonlinkage uses the scalar character and the square-integrable unitary
central character. Thus the square-integrable Langlands classification,
which consumes this theorem, is not an input to its proof.
