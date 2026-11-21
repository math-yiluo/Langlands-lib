# Analyticity of the non-uniqueness locus, from Hartogs's theorem

Module `Langlands.Analysis.Meromorphic.AnalyticComplementReduction`, namespace
`Langlands.Analysis.Meromorphic`.

Setting, as in `MeromorphicContinuationAnalyticComplementStatement`
(module `Langlands.Analysis.Meromorphic.ContinuationPrincipleStatement`): `E` is a complex
normed space (finite-dimensional for the second result); `M` is a connected complex manifold
charted on `E` (`IsManifold 𝓘(ℂ, E) 1 M`); `V` is a complex vector space with a topology
(no continuity of the vector-space operations on `V` is needed here); and the `F i` are
complex Hausdorff locally convex spaces. `μ i s : V →L[ℂ] F i` and `c i s ∈ F i`
form an analytic system (`IsAnalyticSystem`) whose solution sets are locally of finite type
(`IsLocallyFiniteType`), and the unique-solution locus `M_unq = uniqueSolutionLocus μ c` has
nonempty interior. Both results assume Hartogs's theorem on separate holomorphy in the
diagonal form `HartogsDiagonal E` (module `Langlands.Analysis.Meromorphic.WeakComposition`) as
a hypothesis `hH`.

## Results

- `isLocallyCommonZeroSet_compl_uniqueSolutionLocus`: the complement `M ∖ M_unq` is
  `IsLocallyCommonZeroSet` (module `Langlands.Analysis.Meromorphic.CommonZeroSets`) with index
  universe `max uι uF`. Concretely, at every point `s₀` there are a chart ball `W ∋ s₀`, a
  finite-type frame `ℓ : M → (Fin n → ℂ) →L[ℂ] V` and the family indexed by
  `a : Fin n → Σ i, (F i →L[ℂ] ℂ)` of holomorphic functions
  `s ↦ det (scalarMatrix μ ℓ a s)` on `W`, whose common zeros in `W` are exactly
  `W ∖ M_unq`.
- `isAnalyticSubset_compl_uniqueSolutionLocus_of_hartogs`: `M ∖ M_unq` is an analytic subset,
  `IsAnalyticSubset 𝓘(ℂ, E) (uniqueSolutionLocus μ c)ᶜ`.

## Proofs

- At `s₀`, `exists_chartBall_frame` gives a chart ball `W ∋ s₀` with an injective holomorphic
  frame `ℓ` whose ranges contain the solution sets. Because the closure of the interior of
  `M_unq` is all of `M` (`closure_interior_uniqueSolutionLocus_eq_univ`; this uses that `M` is
  connected and `hH`), `W` meets the interior of `M_unq`. Then, for `s ∈ W`,
  `mem_uniqueSolutionLocus_iff_exists_det_ne_zero` says `s ∈ M_unq` iff some minor
  `det (scalarMatrix μ ℓ a s)` is nonzero. So `s ∉ M_unq` iff all these minors vanish at `s`.
  The minors are holomorphic on `W` by `mdifferentiableOn_det_scalarMatrix` (which uses `hH`).
- The second result applies `IsLocallyCommonZeroSet.isAnalyticSubset`, which reduces the
  infinite family of minors to finitely many near each point by the local finiteness theorem
  `Langlands.Analysis.SeveralComplex.exists_finset_zero_iff`.

The results named in the first item are from modules `ContinuationPrincipleReduction` and
`LocalScalarization` (Task 5431).

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`,
Theorem 3.3 (1) (p. 194) and Appendix A (pp. 230–231). Appendix A shows that near each point,
`M_unq` is the union of the nonvanishing loci of the `n × n` determinants of the scalarized
system. The source asserts the analyticity of the complement without a separate argument.
Here the internal theorem `exists_finset_zero_iff` reduces the family of determinants to
finitely many locally. Hartogs's theorem, cited in §3.2, is kept as the explicit hypothesis
`HartogsDiagonal E`.
