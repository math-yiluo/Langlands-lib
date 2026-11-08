# Actual coroot comparison for derived split-torus centralizers

Authors: Worker 1352 and Worker 1577.

`Langlands.GroupScheme.splitTorusCentralizerDerivedCorootComparison` proves
exactly `Langlands.GroupScheme.SplitTorusCentralizerDerivedCorootComparisonStatement.{u}`.
Its type is that published proposition, with the same arbitrary universe `u`.
The statement pair and every pair it imports are unchanged.

The statement covers every algebraically closed field `k : Type u`, connected
reductive group `G`, split subtorus `a : A → G`, arbitrary representative
`j : M → G` of the all-test centralizer of `a`, and actual derived subgroup
`d : D → M` with the explicit premise `IsSemisimple D`. It produces split
maximal tori `i : T → G` and `t : S → D` and a torus morphism `φ : S → T`.
The group map of `φ` is a closed immersion and satisfies `φ ≫ i = t ≫ d ≫ j`.
It also produces finite reduced actual root data `P` of `i` and `Q` of `t`,
a base `b` of `P`, and a subset `s` of `b.support`. The image of the
integral `Q`-coroot span under actual cocharacter postcomposition with `φ`
equals the integral span of the coroots of `P` indexed by `s`.

## Implemented proof

The proof is a single application of the published reduction
`splitTorusCentralizerDerivedCorootComparison_of_rootDatumExistence`
(module `SimplyConnected.SplitTorusCentralizerDerivedCorootComparisonReduction`,
Workers 1352 and 1577). It discharges the reduction's two structural premises
with these unconditional Library theorems:

- `rootDatumExistence : RootDatumExistenceStatement.{u}` (module
  `Reductive.RootDatumExistence`, Worker 835 with Workers 1223 and 1283).
  A split maximal
  torus of a connected reductive group over a field has a finite reduced
  actual root datum. This is Milne, *Algebraic Groups* (2017),
  Theorem 21.11 and Corollary 21.12.
- `dynamicCentralizerReductive : DynamicCentralizerReductiveStatement.{u}`
  (module `Dynamic.CentralizerReductiveProof`, Workers 1325 and 1326).
  Every closed representative of a cocharacter centralizer in a connected
  reductive group is connected reductive.

No other premise remains.

## The reduction being applied

For the supplied data, the reduction does the following. It rewrites the
split-torus centralizer as the dynamic centralizer of a generic integral
cocharacter of `A`. It then proves that the supplied representative `j` is a
closed subgroup, and gets connected reductivity of `M` from
`dynamicCentralizerReductive`. `splitTorusCentralizerSubgroupTorusModel`
then builds compatible actual split maximal tori of `G`, `M` and `D`,
together with the closed torus inclusion `φ`. It does not assume a conjugacy
premise. `rootDatumExistence` applied to `G`, `M` and the semisimple `D`
gives finite reduced actual root data `P`, `R` and `Q`.

The comparison constructor builds an actual central split torus complement
(`derivedTorusCentralComplement`). The product of this complement with the
derived torus maps flatly and surjectively onto the centralizer torus.
`IsRootDatumOf.map_corootSpan_derived` then identifies the image of the
integral `Q`-coroot span with the integral `R`-coroot span. The coroot face
of the centralizer root model (`SplitTorusCentralizerCorootFace`,
Workers 1577 and 1352) supplies a base of `P` and a subset of its support. The integral
span of the coroots in that subset is exactly the `R`-coroot span. By
transitivity, the subset satisfies the displayed equality.

All lattices are the actual character and cocharacter lattices of the
constructed tori. The map is actual integral postcomposition with `φ`, and
no rational span or saturation is used.

## Provenance

This is an internal composition of published Library results. The
mathematical route follows the reduction module's Markdown. The final
theorem only replaces its two explicit premises with their unconditional
published proofs.
