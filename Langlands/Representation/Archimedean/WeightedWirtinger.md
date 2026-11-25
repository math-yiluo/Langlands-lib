# Holomorphic derivatives of weighted functions

Let `T_j` (`j : κ`) be differentiable functions with positive real values (`IsPosReal`),
`ω = ∏_j T_j^{σ_j}` and `D = ∏_j T_j`, and let `φ`, `P` be differentiable with
`φ D^N = ω P`.

- `fderiv_weighted_apply`: at every point `v` and for every direction `w`,
  `Dφ[w] D^{N+1} = ω (Q_w P + D · DP[w] - N P · DD[w])` with
  `Q_w = Σ_j σ_j DT_j[w] ∏_{j' ≠ j} T_{j'}`. (Differentiate the relation; the derivative of `ω`
  times `D` is `ω Q_w`.) This makes explicit, at a point and for a fixed direction, the
  computation behind `exists_fderiv_weighted` (module `WeightedPolynomialDerivative`).
- `wirt_weighted_apply`: the same identity for the complex-linear parts `wirt` of the
  derivatives, obtained from the directions `w` and `i w`.

## Provenance

Internal infrastructure for the proof of `ComplexStandardHolomorphicGrowthStatement`
(Library module `ComplexLinkedLanglandsQuotientGrowth`); see
`ComplexStandardHolomorphicGrowthProof.md` for the overall argument. The module introduces no
statement from the literature, and all its results are proved here.
