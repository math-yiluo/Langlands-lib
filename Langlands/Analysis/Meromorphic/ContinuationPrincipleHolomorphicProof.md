# Proof of openness, holomorphy and meromorphy in the principle of meromorphic continuation

Module `Langlands.Analysis.Meromorphic.ContinuationPrincipleHolomorphicProof`
proves `Langlands.Analysis.Meromorphic.MeromorphicContinuationHolomorphicStatement`
as `meromorphicContinuationHolomorphic`, at the statement's five independent
universes `uE, uM, uV, uι, uF`. That statement is the openness in part (1) and
parts (2) and (3) of Bernstein–Lapid's Theorem 3.3 (the principle of
meromorphic continuation). The function `v` picks the unique solution on the
open locus `M_unq`; it is weakly holomorphic there and meromorphic on the
ambient manifold with `M_unq` as its holomorphy domain. The analyticity of the
complement of `M_unq` in part (1) is neither proved nor used here.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`. The relevant parts
are Theorem 3.3 (p.194), its proof in Appendix A (pp.230–231), and the remark of
§3.2 (p.193) that composites of analytic families are analytic by Hartogs's
theorem.

## Proof

The proof is one application.

- `Langlands.Analysis.Meromorphic.meromorphicContinuationHolomorphic_of_hartogs`
  (module `Langlands.Analysis.Meromorphic.ContinuationPrincipleReduction`)
  proves the statement. It assumes `HartogsDiagonal E` for every
  finite-dimensional complex normed space `E` in universe `uE`. Its Markdown
  describes the route along Appendix A: scalarization in a holomorphic frame,
  Cramer's rule in adjugate form, the identity theorem on chart balls, and the
  density of the interior of `M_unq` by a clopen argument.
- `HartogsDiagonal E` says the following. For open `U ⊆ E` and `G : E → E → ℂ`
  that is complex differentiable on `U` in each variable separately,
  `s ↦ G s s` is complex differentiable on `U`. For finite-dimensional `E`,
  this is exactly the conclusion of
  `Langlands.Analysis.SeveralComplex.differentiableOn_diag_of_separately`
  (module `Langlands.Analysis.SeveralComplex.Hartogs.Basic`, Hartogs's theorem
  on separate holomorphy).

So `meromorphicContinuationHolomorphic` is
`meromorphicContinuationHolomorphic_of_hartogs` applied to
`fun E _ _ _ U G hU h₁ h₂ => differentiableOn_diag_of_separately hU h₁ h₂`. It
uses no hypotheses beyond those of the statement.
