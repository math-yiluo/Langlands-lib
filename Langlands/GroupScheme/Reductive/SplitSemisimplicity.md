# The split semisimplicity criterion

Worker 1407. This module proves the published proposition
`SplitSemisimpleRootDatumStatement` (module
`Langlands.GroupScheme.Reductive.SplitClassificationStatement`) outright, for
an arbitrary universe `u` and every field.

## Main result

- `splitSemisimpleRootDatum : SplitSemisimpleRootDatumStatement.{u}`.
  The proposition is Milne, *Algebraic Groups* (2017), Proposition 21.48 with
  Definition C.34, together with its dual coroot form from the proof of
  Proposition 21.49(a). Let `G` be a connected reductive group over a field
  `k`, `i : T ⟶ G` a maximal torus with `T` split, and `P` a root datum with
  `IsRootDatumOf i P`. Then `G` is semisimple exactly when the roots span a
  subgroup of finite index in the character lattice of `T`, and exactly when
  the coroots span a subgroup of finite index in the cocharacter lattice.
  Semisimplicity, the centre and kernels are the Library's actual-scheme
  notions, so the centre may be nonreduced.

## Proof

The proof is a single application:

    splitSemisimpleRootDatum_of_maximalTorusCentralizer maximalTorusCentralizer

- `splitSemisimpleRootDatum_of_maximalTorusCentralizer` (Worker 1391,
  module `Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanSufficiency`)
  proves
  `MaximalTorusCentralizerStatement.{u} → SplitSemisimpleRootDatumStatement.{u}`.
  It combines the proved "only if" half (roots span a finite-index subgroup
  when `G` is semisimple, module
  `Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity`) with the
  "if" half. The "if" half uses the centralizer statement only to place the
  centre of `G` inside the split maximal torus `T`. The coroot form follows
  from the root form by `splitSemisimpleRootDatum_of_rootSpan` (module
  `Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanReduction`), using
  the rank equality of the root and coroot spans.
- `maximalTorusCentralizer : MaximalTorusCentralizerStatement.{u}`
  (Worker 303, module
  `Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof`, Milne
  Corollary 17.84) proves that a maximal torus of a connected reductive group
  over any field is its own centralizer.

The proof term applies only these two published results and adds no
premise: no cover, realization, factorization law, lifting law or
torus/lattice anti-equivalence witness. The theorem uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.
