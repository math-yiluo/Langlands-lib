# Realization and Lie weights of actual relative root subgroups

`Langlands.GroupScheme.RelativeRoot.rootSubgroupRealization` proves exactly
`Langlands.GroupScheme.RelativeRoot.RootSubgroupRealizationStatement.{u}`,
the existing proposition in
[`RootSubgroupStructureStatement`](RootSubgroupStructureStatement.md).
The universe `u` is arbitrary.

Let `G` be a connected reductive group scheme over any field `k`, and let
`i : S.toGrp ⟶ G` be a maximal split torus. For every actual relative root
`a`, the intrinsic all-test functor `subgroup i a` has a representative
`j : U ⟶ G` which is closed, smooth, connected, unipotent and split
unipotent. The functor is stable under conjugation by `S`, and its Lie
image is `positiveWeightSpan i a`: the sum of the ambient adjoint weight
spaces for every positive integral multiple of `a`.

Here unipotence is the Library's representation-theoretic predicate
`IsUnipotent`. Split unipotence is the existing `IsSplitUnipotent`: a
finite normal series of smooth connected closed subgroups with represented
fppf quotients isomorphic to the one-dimensional vector group, ending
in the group trivial on every scheme test. The Lie-image assertion uses
actual dual-number identity-kernel points and the existing adjoint
weights tested over every coefficient algebra.

The proof assembles published results as follows.

1. Connected reductivity supplies smoothness and affineness of `G`.
   Maximal splitness supplies `IsSplitTorus S.toGrp`, and
   `mem_relativeRoots` gives `a ≠ 0`.
2. `subgroup_isSmoothConnectedClosed_of_ne_zero` from
   [`CyclicRootFunctorComparisonProof`](CyclicRootFunctorComparisonProof.md)
   supplies `U`, `j`, representation of the actual root functor, closedness,
   smoothness and connectedness.
3. `hasLieImage_subgroup` from
   [`RootSubgroupLieImage`](RootSubgroupLieImage.md) identifies the intrinsic
   Lie image with `semigroupWeightSpan` for `cyclicTail a 1`. The private
   lemma `cyclicSpan_eq_positive` proves its equality with
   `positiveWeightSpan i a` by the two inclusions of the indexed suprema.
   A cyclic-tail index is a positive natural multiple, and conversely every
   positive natural multiple supplies such an index.
   `actionWeightSpace_conjugation` identifies the two weight conventions.
4. Since `j` is closed and `G` is affine, `U` is affine. Give `U` its actual
   induced torus action `b = subgroupAction i a j hj`.
   `subgroupAction_zero_weightSpace_eq_bot_of_hasLieImage` from
   [`RootSubgroupWeightExclusion`](RootSubgroupWeightExclusion.md) uses the
   exact positive Lie image and `a ≠ 0` to prove
   `actionWeightSpace b 0 = ⊥`.
5. Apply the published
   [`torusActionUnipotence`](TorusUnipotenceProof.md) to this same smooth
   connected affine `U`, split torus and action. Then apply
   [`torusActionSplitUnipotence`](TorusSplitUnipotenceProof.md), using the
   unipotence just proved. These give `IsUnipotent U` and
   `IsSplitUnipotent U` without additional premises.
6. Assemble these conclusions with `subgroup_isStable` from
   [`RootSubgroupStabilityProof`](RootSubgroupStabilityProof.md), which
   proves actual conjugation stability on all tests, and the Lie image
   from step 3.

This is an internal assembly of the published constructions and proofs.
Its source scope is the unchanged proposition documented in
`RootSubgroupStructureStatement.md`; the present file adds no external
source assertion. It retains arbitrary fields and universes, imperfect
fields, every characteristic, non-split connected reductive groups and
nonreduced relative root systems. Every positive multiple is retained.
Representability, the geometry and both unipotence assertions are
conclusions.

Worker 1285 wrote the assembly and its reindexing lemma. The imported
cyclic comparison and root Lie-image developments are due to Workers
1283 and 1300. The imported torus unipotence proof is due to Workers
1388 and 1398, and the splitness proof to Workers 1389 and 1419, using
Worker 1324's grading adapter and Worker 1285's coordinate comparison.
Those results are reused from the Library by Lean module name.
