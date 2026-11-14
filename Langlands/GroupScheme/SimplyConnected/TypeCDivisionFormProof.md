# The type-C division-form classification: proof

Proof of `Langlands.GroupScheme.TypeCDivisionFormStatement` (module
`Langlands.GroupScheme.SimplyConnected.TypeCDivisionFormStatement`):

```lean
theorem Langlands.GroupScheme.typeCDivisionForm : TypeCDivisionFormStatement.{u}
```

Authors: Worker 31, with Worker 161 (the split-rank input), for Task 5986
(`8494af77-9d10-4c2f-b1cd-60dc371fb195`). The theorem's type is exactly the published statement
at every universe `u`. It has no extra hypothesis and holds over every field, in every
characteristic. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Statement

Let `K` be a field and `G` an affine, locally finite type group scheme over `Spec K`. Suppose
`G` is simply connected and absolutely almost simple. Let `d : TitsIndexData G` be actual
index data and `e : d.Vertex ≃ Fin n`, `2 ≤ n`, a numbering under which `d.cartan` is
`CartanMatrix.C n`. Then there are `degree > 0`, `m` with `NeZero m` and
`m * degree = 2 * n`, and a central division algebra `D` with `dim_K D = degree ^ 2`. There
is also an involution of the first kind `σ` on `D` whose symmetric subspace has dimension
`degree * (degree + 1) / 2`, and an invertible trace-valued `σ`-antihermitian `H ∈ M_m(D)`.
These satisfy `σ.wittIndex H = splitRank G` and `G ≅ σ.symplecticGroup H`. A vertex `a` is
distinguished exactly when `(e a).val + 1 = j * degree` for some `1 ≤ j ≤ splitRank G`.

## Proof

The theorem applies the reduction `typeCDivisionForm_of_inputs` (module
`SimplyConnected.TypeCDivisionFormReduction`) to proofs of its four inputs:

1. `typeCQuasiSplitInnerForm : TypeCQuasiSplitInnerFormStatement` (module
   `SimplyConnected.TypeCQuasiSplitInnerFormProof`, in this candidate): `G` has a quasi-split
   inner-form presentation whose model is `Sp_{2n}`.
2. `symplecticInnerFormAntihermitian : SymplecticInnerFormAntihermitianStatement` (published,
   module `SimplyConnected.SymplecticInnerFormAntihermitianProof`): every inner form of
   `Sp_{2n}` is isomorphic to `σ.symplecticGroup H` for data as in the conclusion.
3. `antihermitianSymplecticSplitRank : AntihermitianSymplecticSplitRankStatement` (module
   `Quaternionic.AntihermitianSplitRankProof`, in this candidate): the split rank of
   `σ.symplecticGroup H` is `σ.wittIndex H`.
4. `typeCDistinguishedVertices : TypeCDistinguishedVerticesStatement` (published, module
   `SimplyConnected.TypeCDistinguishedVerticesProof`): the distinguished vertices are those
   numbered `j * degree` for `1 ≤ j ≤ σ.wittIndex H`.

The reduction obtains the inner form from 1 and the division-algebra data and isomorphism from
2. It moves the split rank along that isomorphism (`splitRank_eq_of_iso`) and identifies it
with the Witt index by 3. With this equality, 4 gives the vertex clause. Each input's
Markdown describes its own proof.

## Literature

J. Tits, *Classification of algebraic semisimple groups* (1966), Table II, type `C_n`,
printed p.56 (source `tits-1966-classification-algebraic-semisimple`). Knus–Merkurjev–Rost–
Tignol, *The Book of Involutions*, Theorem (26.14), printed p.369 (source
`knus-merkurjev-rost-tignol-1998-book-of-involutions`). The Lean route follows the classical
argument: a type-`C_n` group is an inner form of `Sp_{2n}` because the `C_n` diagram has no
symmetry; such inner forms are symplectic groups of antihermitian forms over division
algebras; and the index is read off a maximal split torus built from a Witt decomposition.
