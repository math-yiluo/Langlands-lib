# Index comparisons for an aligned type-D spin cover

Authors: Worker 146.

This module proves `Langlands.GroupScheme.AlignedSpinCoverTitsIndexStatement` (Task 6282) as
the theorem

```lean
theorem Langlands.GroupScheme.alignedSpinCoverTitsIndex :
    AlignedSpinCoverTitsIndexStatement.{u}
```

for every universe `u`. The only axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

## The statement

Let `K` be a field and `G` an affine group scheme of locally finite type over `Spec K`
with Tits index data `d`, numbered by `e : d.Vertex ≃ Fin n` (`4 ≤ n`) compatibly with
`CartanMatrix.D n`. Assume `G` is simply connected and absolutely almost simple. Let `D`
be a central division algebra of degree `degree` with `m * degree = 2 * n`, `σ` a
first-kind involution with `finrank K σ.symmetricSubspace = degree * (degree + 1) / 2`,
`q` a nondegenerate `σ`-quadratic form on `D^m`, and `π : G ⟶ σ.isometryGroup q` with
`σ.IsSpinCover q π` and `d.FundamentalWeightTrivialOnKernel v π` for the vertex `v`
numbered `0`. Then

- `σ.quadraticWittIndex q = splitRank G`;
- for every vertex `a` with `(e a).val + 2 < n`, `a` is distinguished exactly when
  `(e a).val + 1 = j * degree` for some `0 < j ≤ σ.quadraticWittIndex q`.

All fields and characteristics, characteristic 2 and finite fields included, and all
universes are covered. The star-action hypothesis of the statement is not used.

## The proof

The proof is a one-line composition.

1. `Langlands.GroupScheme.alignedSpinCoverTitsIndex_of_weights`, from the helper module
   `Langlands.GroupScheme.SimplyConnected.AlignedSpinCoverTitsIndexReduction` of this
   contribution, derives the statement from three hypotheses:
   `Quaternionic.ConnectedIsometrySplitRankStatement`,
   `Quaternionic.IsometryMaximalSplitTorusWeightsStatement` and
   `SpinCoverVectorWeightsStatement`. Its Markdown describes the argument: compare split
   ranks through the central isogeny `G ⟶ O(q)⁰`, push the split torus of `d` onto a
   maximal split torus of `O(q)⁰`, perturb the positive cocharacter so that it pairs
   nonzero with all relevant characters, and compare weight multiplicities on `D^m`
   with those of the vector characters. The counting lemma
   `Langlands.Combinatorics.MultiplicityJumps.chain_ne_succ_iff`, from the second helper
   module `Langlands.Combinatorics.MultiplicityJumps`, turns the multiplicity identity
   into the jump criterion `(e a).val + 1 = j * degree`.
2. The first two hypotheses are the published theorems
   `Langlands.GroupScheme.Quaternionic.connectedIsometrySplitRank` and
   `Langlands.GroupScheme.Quaternionic.isometryMaximalSplitTorusWeights`.
3. The third hypothesis is
   `Langlands.GroupScheme.spinCoverVectorWeights_of_representation_inputs` applied to
   the published theorems `Langlands.GroupScheme.Quaternionic.orthogonalMoritaRepresentation`
   and `Langlands.GroupScheme.OrthogonalMatrix.numberedCoverVector`.

## Files

- `Langlands/GroupScheme/SimplyConnected/AlignedSpinCoverTitsIndex.lean`: this theorem.
- `Langlands/GroupScheme/SimplyConnected/AlignedSpinCoverTitsIndexReduction.lean`: the
  reduction `alignedSpinCoverTitsIndex_of_weights` and its helper lemmas.
- `Langlands/Combinatorics/MultiplicityJumps.lean`: the counting lemmas on signed
  multiplicities used in the last step of the reduction.
