# Scalar real parts on arbitrary actual block tensors

`Langlands.blockTensorScalarRealPart` is an internal scalar calculation for
actual smooth complex block factors. Worker 320 supplied the Lean proof;
Worker 544 checked its published inputs and prepared the paired documentation.

Let `Y i` be a smooth representation of the block `GL_(B.size i)(F)`, with
supplied scalar character `c i` and real coordinate `x i` satisfying
`‖c i a‖ = T.normalizedAbs a ^ x i` for every scalar unit `a`. For any
permutation `e` sending new positions to original labels, the character

`χ(a) = ∏ i, c (e i) (a i)`

acts on the split centre of the actual external tensor of `Y (e i)` for the
permuted block shape `B.permute e`. Its real part is exactly `x ∘ e` in the
Library's block-scalar coordinates. The permutation retains original positions,
even when factors, characters or coordinates coincide.

The proof applies
`GeneralLinear.BlockShape.hasScalarCharacter_blockTensor_splitCentre` from
[`DescendingIntervalBlockScalarProof`](DescendingIntervalBlockScalarProof.md)
to the permuted family. The shape and relabelling are the actual definitions
in [`BlockPermutation`](../CuspidalSupport/BlockPermutation.md). Evaluating the
finite product of characters, coercing units and taking norms reduces
[`T.IsRealPartOf`](Jacquet.md) to the supplied individual norm identities.
There is no additional degree factor: the supplied `x i` already measures
scalar coordinates.

This is a derived generic scalar-tensor calculation, with arbitrary smooth
block factors and no new original-literature claim. It requires no
nontriviality, irreducibility, finite length, Jacquet occurrence, induction
embedding or analytic hypothesis. The independent field and carrier universes
are retained; saturated carriers follow by specializing the carrier universe.
