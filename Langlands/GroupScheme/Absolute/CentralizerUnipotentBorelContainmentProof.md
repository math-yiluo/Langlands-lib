# Proof: normal unipotent subgroups of cocharacter centralizers lie in ambient Borels

Module `Langlands.GroupScheme.Absolute.CentralizerUnipotentBorelContainmentProof` proves

```lean
theorem Langlands.GroupScheme.centralizerUnipotentBorelContainment :
    CentralizerUnipotentBorelContainmentStatement.{u}
```

The theorem's type is exactly the unchanged published proposition, at an arbitrary universe `u`.
It has the target's hypotheses and no others. Let `k` be algebraically closed and `G` smooth,
connected and affine over `Spec k`. Let `χ` be any cocharacter, trivial or noninjective
included. Let `j : M ⟶ G` be a closed representative of its dynamic centralizer, with `M`
smooth and connected. Let `i : U ⟶ M` be a smooth connected unipotent closed subgroup that is
normal in `M`. For every Borel subgroup `b : B ⟶ G` whose range contains `χ`, the range of
`i ≫ j` lies in the range of `b` on every test scheme.

## Proof

The proof applies the published reduction
`centralizerUnipotentBorelContainment_of_statements`
(`Absolute.CentralizerUnipotentBorelContainmentReduction`) to two published theorems:

- `centralizerBorelIntersection : CentralizerBorelIntersectionStatement.{u}`
  (`Absolute.CentralizerBorelIntersectionProof`). A Borel subgroup `b` of `G` containing `χ`
  contains a Borel subgroup `c : C ⟶ M` of the represented centralizer, in the sense
  `range (c ≫ j) ≤ range b`. This is the existence part of Milne 2017, Theorem 17.46, in
  cocharacter form.
- `normalUnipotentBorelContainment : NormalUnipotentBorelContainmentStatement.{u}`
  (`Absolute.NormalUnipotentBorelContainmentProof`). A smooth connected unipotent normal
  closed subgroup of a smooth connected affine group lies in each of its Borel subgroups. Here
  it is applied inside `M`, which gives `range i ≤ range c`.

The reduction pushes `range i ≤ range c` forward along `j` with
`SubgroupFunctor.range_comp_mono` and combines the result with `range (c ≫ j) ≤ range b`.
The `.md` file of the reduction gives the details. Every containment is on all test schemes.

## Provenance

The route follows J. S. Milne, *Algebraic Groups* (2017). The Borel-containment step in the
proof of Corollary 17.57 (printed p. 371) uses Theorem 17.46 (printed pp. 365–366) together
with containment of a normal unipotent subgroup in every Borel (Remark 17.31, printed p. 361).
Milne passes through the scheme-theoretic image of `χ`. The Lean proof does not: it uses the
cocharacter form of the intersection theorem directly, and the published proof
`centralizerBorelIntersection` handles the cocharacter on its own terms.

This module only assembles the pieces. No imported statement or its
documentation is changed.
