# Groups of multiplicative type are closed subgroups of tori

This module proves the statement
`Langlands.GroupScheme.MultiplicativeTypeTorusEmbeddingStatement` (Conrad,
*Reductive group schemes* (2014), Proposition B.3.8) in every universe `u`:

```lean
theorem multiplicativeTypeTorusEmbedding : MultiplicativeTypeTorusEmbeddingStatement.{u}
```

So for every scheme `S` and every group scheme `H` over `S` with
`RelativeMultiplicativeType.IsMultiplicativeType H`, there are a group scheme
`T` over `S` with `RelativeTorus.IsTorus T` and a homomorphism `i : H ⟶ T`
with `IsClosedSubgroup i` (a closed immersion). There are no further
hypotheses. The theorem depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Lean proof

`IsMultiplicativeType H` provides a cover `𝒰` of `S` for the precoverage
`Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)` (that is,
Mathlib's `Scheme.fppfPrecoverage`). Over each member `𝒰.f i`, the base change
of `H` is diagonalizable.

- `DiagonalizableAtlas.ofCover 𝒰 h𝒰` is the `DiagonalizableAtlas H` (module
  `DiagonalizableAtlasComparison`) with charts `𝒰.f i`. Its character groups
  `Λ i` and trivializations `(𝒰.f i)*H ≅ D(Λ i)` are chosen from the
  diagonalizability witnesses.
- Its projection `∐ 𝒰.X i ⟶ S` is `Sigma.desc 𝒰.f`. It is flat
  (`ofCover_flat`, Mathlib's instance for `Sigma.desc` of flat maps), locally
  of finite presentation (`ofCover_locallyOfFinitePresentation`, by locality
  at the source, `IsZariskiLocalAtSource.sigmaDesc`), and surjective
  (`ofCover_surjective`, since the cover is jointly surjective:
  `Surjective.sigmaDesc_of_union_range_eq_univ` with `𝒰.iUnion_range`).
- With `A = ofCover 𝒰 h𝒰`, take `T = A.torus` and `i = A.torusEmbedding`
  (module `MultiplicativeTypeAtlasEmbedding`). `A.isClosedSubgroup_torusEmbedding`
  shows that `i` is a closed immersion.
- `A.isSplitTorus_baseChange_torus j` shows that `(𝒰.f j)*T` is a split
  torus, hence a torus (`RelativeTorus.IsTorus.of_isSplitTorus`). The
  Library's `RelativeTorus.IsTorus.of_fppfCover` (module
  `Langlands.GroupScheme.Torus.FppfRelativeTorusDescent`) applied to `𝒰` gives
  `RelativeTorus.IsTorus T`.

## Outline of the construction

The supporting modules carry out Conrad's argument as follows.

1. `FreeCharacterCover`: each finitely generated `Λ` gets a free cover
   `F(Λ) = Λ ×_{Λ/eΛ} ℤ[Λ/eΛ] ↠ Λ`, where `e` is the order of the torsion of
   `Λ`. The cover is functorial in isomorphisms of `Λ`. So
   `D(Λ) ⟶ D(F(Λ))` is a closed embedding into a split torus
   (`FreeCharacterCoverTorus`).
2. `DiagonalizableIsoLift`: any isomorphism `D_X(Λ) ≅ D_X(Λ')` is locally
   `D(g)` (local rigidity, `RelativeDiagonalizableHomLocality`).
   It therefore lifts canonically to `D_X(F(Λ)) ≅ D_X(F(Λ'))`, compatibly with
   pullback and composition.
3. `MultiplicativeTypeAtlas`: the split tori `D(F(Λ i))` are glued over
   `∐ 𝒰.X i` (`Descent/DisjointGroupGluing`). The lifted
   comparisons form a descent datum along the fppf map `∐ 𝒰.X i ⟶ S`.
4. `MultiplicativeTypeAtlasEmbedding`: the closed embeddings `D(proj)` glue
   to an embedding compatible with the data. The fppf descent modules
   `Descent/Fppf*` (fppf versions of the Library's étale descent modules)
   descend the group and the embedding to `S`. Closedness descends along
   fppf maps, and the descended group is split on every chart.
