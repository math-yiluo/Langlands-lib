# Assembly of the full cuspidal Jacquet modules of segment constituents

Author: Worker 964.

Module `Langlands.Representation.Classification.SegmentFullJacquetAssembly`,
namespace `Langlands.SegmentFullJacquet`. This is an internal helper for the proof
of `Langlands.Classification.SegmentFullJacquetFormula` (Zelevinsky 1980, 3.1 and
9.1(*)). Its two main theorems are conditional: the associated Jacquet filtration
and the Jacquet filtrations of the edge representations are hypotheses. The final
proof module discharges them with published results.

Notation: `β = BlockShape.uniform m r hr`, `A` a supercuspidal representation of
`GL_r`, `σ i = ν^i A` the increasing segment factors, `I = i(σ)` the segment
induction, `J = r_β(I)` its normalized Jacquet module along `β`, and
`γ = β.adjacentMerge k hk` the shape merging blocks `k` and `k + 1`.

## Helpers

- `isIrreducible_permutedSegmentTensor`: the segment tensor with permuted factors
  is irreducible (published `CuspidalSupport.glCuspidalTensor` with the factors
  `segmentSupercuspidalFactor`).
- `exists_hasScalarCharacter`: a supercuspidal representation has a scalar
  character on the scalar matrices (published `admissibleSchur_centralCharacter`).

## Subrepresentation clause

`subrepresentation_jacquet_equiv` assumes:

- `hassoc : AssociatedJacquetFiltrationTheorem F T (m * r)`;
- `hm : 0 < m`, `hr : 0 < r` and a supercuspidal `A` of `GL_r`;
- `hedge`: for every `k` with `k + 1 < m` there are factors `Y` on `γ`, an actual
  filtration of `r_β(i_γ(Y))` whose graded pieces are equivalent to the transports
  of the segment tensor with `k` and `k + 1` exchanged, indexed by the minimal
  self-conjugating permutations that are also minimal for `(γ, β)`, and a
  surjective intertwiner `I → i_γ(Y)`. This is the form produced by the published
  `SegmentEdgeJacquetFiltration` with `Y` the quotient of Ze80 1.11 in the merged
  slot.

Then every irreducible subrepresentation `π` of `I`
(`Classification.IsIrreducibleSubrepresentation`) has `r_β(π)` equivalent to the
increasing segment tensor. Proof:

1. `exists_segmentJacquetFiltration` filters `J` with irreducible pieces. The
   separating scalar `z` acts on the piece indexed by `w` through the scalar
   `c w = segmentScalar(blockPerm w)`, and these scalars are pairwise distinct.
2. The Jacquet map `ι : r_β(π) → J` of the embedding is injective. Frobenius
   reciprocity gives a nonzero map `r_β(π) → σ_0 ⊗ ⋯ ⊗ σ_(m-1)`, on which `z` acts
   by the scalar of the identity block permutation.
3. Separation: for every other index, the block permutation `g` has a descent at
   some `k` (`exists_descent_of_ne_one`). Take the edge data for `k`. The pieces of
   `r_β(i_γ(Y))` carry the scalars of the block permutations `blockPerm v * swap`
   (`transport_permuted_separatingScalar`). By
   `isMinimalRepresentative_adjacentMerge_iff` these are exactly the permutations
   with a descent at `k`. So `g` occurs and the identity does not. The Jacquet map
   of the surjection is surjective. Its composite with `ι` is the Jacquet map of
   `π → I → i_γ(Y)`, which is injective or zero because `π` is irreducible.
4. The isolation lemma `CentralEigenspaceSplitting.nonempty_equiv_graded_of_sub`
   gives `r_β(π) ≃` the identity piece. That piece is equivalent to the transport
   by the identity block permutation (`hsEq`). The transport is equivalent to the
   segment tensor itself (`nonempty_transport_equiv_permuted`).

## Quotient clause

`quotient_jacquet_equiv` assumes `hassoc`, `hm`, `hr`, a supercuspidal `A` and, for every `k`, edge data whose
pieces are the transports of the increasing tensor itself (the published
`SegmentEdgeJacquetFiltration` with `Y` the subrepresentation of Ze80 1.11 in the
merged slot), together with an injective intertwiner `i_γ(Y) → I`. Then every
irreducible quotient `π` of `I` (`Classification.IsIrreducibleQuotient`) has `r_β(π)` equivalent to the decreasing segment
tensor `ν^(m-1)A ⊗ ⋯ ⊗ A`. Proof:

1. As above, `J` is filtered and split by `z`. The Jacquet map `J → r_β(π)` of the
   quotient map is surjective.
2. Second adjointness (`exists_reversedTensor_to_jacquet_ne_zero`) gives a nonzero
   map from the increasing tensor, pulled back along block reversal, into
   `r_β(π)`. `z` acts on its source by the scalar of the reversal permutation.
3. Separation: every block permutation other than the reversal has an ascent at
   some `k` (`exists_ascent_of_ne_rev`). The pieces of `r_β(i_γ(Y))` carry exactly
   the permutations with an ascent at `k`. The Jacquet map of the injection is
   injective. Its composite with the quotient map is the Jacquet map of
   `i_γ(Y) → I → π`, which is surjective or zero because `π` is irreducible.
4. The isolation lemma `CentralEigenspaceSplitting.nonempty_equiv_graded_of_quot`
   gives the reversal piece `≃ r_β(π)`. The reversal piece is equivalent to the
   segment tensor with factors `i ↦ ν^(rev i) A`. This is the decreasing tensor,
   since `rev i = m - 1 - i` (`Fin.val_rev`).
