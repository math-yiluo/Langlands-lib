# Classical type-`D` spin presentations with index comparisons

The two theorems it uses are `classicalTypeDAlignedSpinCover` and
`alignedSpinCoverTitsIndex`.

Module `Langlands.GroupScheme.SimplyConnected.ClassicalTypeDSpinPresentationProof`.

## Statement

```lean
theorem Langlands.GroupScheme.classicalTypeDSpinPresentation :
    ClassicalTypeDSpinPresentationStatement.{u}
```

This proves the Library proposition `ClassicalTypeDSpinPresentationStatement` at
every universe `u`, with no extra hypotheses. Let `K` be a field and `G` an affine group
scheme of locally finite type over `Spec K`. Let `d` be Tits index data for `G` with vertices
numbered by `e : d.Vertex ≃ Fin n`, `4 ≤ n`, and Cartan matrix `CartanMatrix.D n`. Assume
`G` is simply connected and absolutely almost simple, and every `γ ∈ Gal(K^s/K)` acts by the
star action as the identity on each vertex numbered `i` with `i + 2 < n` (the nonfork
vertices). Then there are:

- a central, finite-dimensional division `K`-algebra `D` with `finrank K D = degree ^ 2` and
  `0 < degree`;
- a natural number `m` with `m * degree = 2 * n`;
- a first-kind involution `σ` of `D` with
  `finrank K σ.symmetricSubspace = degree * (degree + 1) / 2` (Tits's type-1 condition,
  natural-number division);
- a nondegenerate `σ`-quadratic form `q` on `D^m` whose Witt index
  `σ.quadraticWittIndex q` equals `splitRank G`;
- for every nonfork vertex `a`, `a ∈ d.distinguishedVertices` exactly when
  `(e a).val + 1 = j * degree` for some `j` with `0 < j ≤ σ.quadraticWittIndex q`;
- a morphism `π : G ⟶ σ.isometryGroup q` with `σ.IsSpinCover q π`. So `π` is a central
  isogeny onto the identity component `O(q)⁰`, `O(q)` is smooth, and `G` is simply
  connected.

All fields are covered, in every characteristic, including characteristic 2 and finite
fields. The case `n = 4` is included.

## Proof

The proof is one application of `classicalTypeDSpinPresentation_of_aligned` (module
`ClassicalTypeDSpinPresentationReduction`). That reduction derives the target
from two propositions. The proof supplies a Library proof of each:

1. `ClassicalTypeDAlignedSpinCoverStatement`, proved by
   `Langlands.GroupScheme.classicalTypeDAlignedSpinCover` (module
   `ClassicalTypeDAlignedSpinCoverProof`). Under the target's hypotheses it gives `D`,
   `degree`, `m`, `σ` and a nondegenerate `q` with the dimension facts above. It also gives
   a spin cover `π : G ⟶ O(q)` such that the fundamental weight at the vertex numbered `0`
   is trivial on `ker π`.
2. `AlignedSpinCoverTitsIndexStatement`, proved by
   `Langlands.GroupScheme.alignedSpinCoverTitsIndex` (module `AlignedSpinCoverTitsIndex`).
   For every such aligned spin cover it proves `σ.quadraticWittIndex q = splitRank G` and
   the description of the nonfork distinguished vertices.

The reduction applies the first theorem to the given data. It feeds the witnesses and the
alignment into the second theorem for the same `K, G, d, n, e`, and returns those witnesses
with both conclusions.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. None of
`TypeDRankOneSpinStatement`, `LocalRankOneClassificationStatement`,
`LocalAbsolutelyAlmostSimpleRankOneKneserTitsStatement`, `LocalRankOneKneserTitsStatement`
or `LocalKneserTitsStatement` is named in any module of its import closure.

## Provenance

Internal assembly. The mathematics is the classification of the forms of type `D_n` through
spin groups of quadratic forms over division algebras with an orthogonal involution, and the
reading of the Tits index from the Witt index and the division degree (J. Tits,
*Classification of algebraic semisimple groups*, 1966, Table II; registered source
`tits-1966-classification-algebraic-semisimple`). Exact page locators are in
`ClassicalTypeDSpinPresentationStatement.md`. The sources and arguments of the two inputs
are in `ClassicalTypeDAlignedSpinCoverStatement.md`, `AlignedSpinCoverTitsIndexStatement.md`
and the Markdown of the two cited proofs. The proof here follows no literature argument of
its own: it only composes those Library theorems.
