# Proof that the non-uniqueness locus is analytic

Module `Langlands.Analysis.Meromorphic.ContinuationPrincipleAnalyticComplementProof`, namespace
`Langlands.Analysis.Meromorphic`.

## Results

- `hartogsDiagonal_of_finiteDimensional E`: for every finite-dimensional complex normed space
  `E`, `HartogsDiagonal E` holds. This is the diagonal form of Hartogs's theorem on separate
  holomorphy: if `U ⊆ E` is open and `G : E → E → ℂ` is complex differentiable on `U` in each
  argument separately (with the other argument in `U`), then `s ↦ G s s` is complex
  differentiable on `U`.
- `meromorphicContinuationAnalyticComplement`: a proof of the Library statement
  `MeromorphicContinuationAnalyticComplementStatement.{uE, uM, uV, uι, uF}` (module
  `Langlands.Analysis.Meromorphic.ContinuationPrincipleStatement`), unchanged. For every
  analytic system of linear equations `μ, c` on a connected complex manifold `M` modelled on a
  finite-dimensional `E`, whose solution sets are locally of finite type and whose
  unique-solution locus `M_unq` has nonempty interior, the complement `M ∖ M_unq` is an
  analytic subset of `M` (`IsAnalyticSubset 𝓘(ℂ, E) (uniqueSolutionLocus μ c)ᶜ`).

## Proofs

- `hartogsDiagonal_of_finiteDimensional` is
  `Langlands.Analysis.SeveralComplex.differentiableOn_diag_of_separately` (module
  `Langlands.Analysis.SeveralComplex.Hartogs.Basic`), whose hypotheses are exactly those in the
  definition of `HartogsDiagonal` (module `Langlands.Analysis.Meromorphic.WeakComposition`).
- `meromorphicContinuationAnalyticComplement` introduces the data and hypotheses of the
  statement and applies `isAnalyticSubset_compl_uniqueSolutionLocus_of_hartogs` (module
  `Langlands.Analysis.Meromorphic.AnalyticComplementReduction`) with
  `hartogsDiagonal_of_finiteDimensional E`. That reduction shows that near each point the
  complement is the common zero set, on a chart ball, of the holomorphic family of all `n × n`
  minors of the scalarized system. It then uses the local finiteness theorem
  `Langlands.Analysis.SeveralComplex.exists_finset_zero_iff`, transferred to manifolds by
  `IsLocallyCommonZeroSet.isAnalyticSubset`, to replace this family by finitely many minors
  near each point. The reduction only needs a topology on the complex vector space `V`,
  but the theorem retains all the instances in the published statement.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`,
Theorem 3.3 (1) (p. 194). The determinant description of the unique-solution locus comes from
Appendix A (pp. 230–231). For the operator composition step, §3.2 cites Hartogs's theorem
(Krantz, *Function Theory of Several Complex Variables*, §0.2 and Theorem 1.2.5).

The passage from infinitely many determinants to finitely many uses the internal local
finiteness theorem `exists_finset_zero_iff`. The source does not give a separate argument for
this passage. The Library's statement Markdown points to Noetherianity of convergent power
series; the implemented proof neither proves nor uses that result or Weierstrass preparation.
It addresses the analyticity assertion, not the other conjunct of the continuation principle.
