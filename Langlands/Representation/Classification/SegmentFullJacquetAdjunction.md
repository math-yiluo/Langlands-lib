# Nonzero maps out of and into the Jacquet module of a segment constituent

Author: Worker 964.

Module `Langlands.Representation.Classification.SegmentFullJacquetAdjunction`,
namespace `Langlands.SegmentFullJacquet`. This is an internal helper for the proof
of `Langlands.Classification.SegmentFullJacquetFormula`. Throughout,
`β = BlockShape.uniform m r hr` and `I = T.segmentInduced A m hr`.

- `exists_jacquet_to_tensor_ne_zero` (first adjointness, Frobenius reciprocity). A
  nonzero intertwiner `j : π → I` gives a nonzero intertwiner from the normalized
  Jacquet module of `π` along `β` to the increasing segment tensor. It is the image
  of `j` under the published linear equivalence
  `Parabolic.FirstAdjointness.equiv` (Casselman, Proposition III.3.5). The product
  induction is the parabolic induction of the block tensor by definition.
- `isAdmissible_of_segmentQuotient`. If `A` is admissible, every quotient of `I` is
  admissible. Use `segmentInductionAdmissibility` and
  `Unramified.SphericalExistence.isAdmissible_of_surjective`. Small compact open
  subgroups come from `exists_compactOpenSubgroup_hasBlockIwahoriFactorization`.
- `uniformReverse F m r hr`: the automorphism `x ↦ (i ↦ x (rev i))` of the uniform
  Levi. It reverses the order of the blocks.
- `exists_reversedTensor_to_jacquet_ne_zero` (second adjointness). For `0 < m`,
  admissible `A` and a nonzero surjective intertwiner `q : I → π`, there is a nonzero
  intertwiner from the increasing segment tensor, pulled back along
  `uniformReverse`, to the normalized Jacquet module of `π` along `β`. Proof:
  `π` is admissible by the previous lemma. The published second adjointness
  `Parabolic.normalizedSecondAdjointness` turns `q` into a nonzero map from the
  increasing tensor to the opposite normalized Jacquet module of `π`. The published
  `oppositeJacquetReverseEquiv` identifies that module with the upper normalized
  Jacquet module along `β.reverse`, pulled back along `leviReverseEquiv β`.
  For the uniform shape, `β.reverse` is definitionally `β`. Composing with
  `uniformReverse` undoes the pullback, since `leviReverseEquiv β ∘ uniformReverse`
  is the identity (`Fin.rev_rev`).

The separating scalar acts on the pulled-back tensor through the reversed block
permutation. This is used for the quotient clause in
`SegmentFullJacquetAssembly`.
