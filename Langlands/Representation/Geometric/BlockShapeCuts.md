# Ordered block shapes and interior cuts

Author: Worker 320.

This derived supporting construction identifies the Library's actual ordered
positive `Langlands.GeneralLinear.BlockShape n` with finite sets of interior
cuts. It applies to every natural rank, including zero.

`ofComposition` uses a Mathlib composition's length and indexed positive
parts as the fields of a block shape. Its positivity and total-sum proofs
are the corresponding intrinsic composition laws. The existing
`toComposition` sends a shape to the list `List.ofFn B.size`.
`toComposition_ofComposition` follows from `Composition.ofFn_blocksFun`;
the other inverse law follows from the published injectivity of
`toComposition`. These maps and inverse laws form `BlockShape.compositionEquiv`.

`BlockShape.cutEquiv n` composes this equivalence with Mathlib's
`compositionEquiv n` and `compositionAsSetEquiv n`. Its value `B.cuts` is a
`Finset (Fin (n - 1))`. The two inverse laws and injectivity are exposed as
intrinsic identities.

The membership law `mem_cuts_iff` fixes the indexing convention: `i` is a
cut precisely when the position `i.val + 1` belongs to
`B.toComposition.boundaries`. Thus these are cuts between consecutive
coordinates, with both outside endpoints omitted. At rank zero or one the
cut type is empty; the equivalence still applies without a positive-rank
hypothesis.

The provenance is the existing block-shape and finite-composition
constructions, together with Mathlib's
`Mathlib.Combinatorics.Enumerative.Composition`. No external mathematical
theorem is asserted here. This adapter is intended for finite combinatorial
sums in the segment-classification proof route. It proves no alternating
coefficient identity, representation-theoretic duality, or classification
statement.
