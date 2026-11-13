# Reduction of the type-D spin presentation to an aligned cover

Author: Worker 64.

`Langlands.GroupScheme.classicalTypeDSpinPresentation_of_aligned` is the
theorem

```
ClassicalTypeDAlignedSpinCoverStatement.{u} →
  AlignedSpinCoverTitsIndexStatement.{u} →
    ClassicalTypeDSpinPresentationStatement.{u}
```

Both premises are explicit and unproved. The theorem does not prove
`ClassicalTypeDSpinPresentationStatement` unconditionally.

## Proof

Fix the data `K, G, d, n, e` and the hypotheses of the target. The
existence statement gives `D`, `degree`, `m`, `σ`, `q` and `π`, with the
dimension facts, nondegeneracy, `IsSpinCover` and the alignment at the
vertex numbered `0`. These are exactly the inputs of the index
comparison, applied to the same `K, G, d, n, e` and hypotheses. It
returns the Witt-index equality and the nonfork vertex formula. The
target's existential is then filled with the same witnesses. The
division-ring, algebra, centrality and finite-dimensionality instances
are those obtained from the first premise, passed as `inferInstance`.
The proof uses only `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Internal. The theorem only reorders the conclusions of the two premises.
The mathematical sources are cited in
`ClassicalTypeDAlignedSpinCoverStatement.md` and
`AlignedSpinCoverTitsIndexStatement.md`.
