# The normalized real Godement restrictions at the exact local points

This module is the real counterpart of the Library's `ComplexGapExactRestriction`. Notation as in
`RealGapNormalizedRestriction` with `k = t + 1` and `n = t + 1 + q + 1`.

* `dual_realAdjacentGodementCoefficient`: if `U ∈ realUniformWhittakerModel r ds (−a)` and its dual
  `Ũ = dualFunction U` lies in `realUniformWhittakerModel r dds a`, then the dual of
  `realAdjacentGodementCoefficient D a Φ U c` at `g` is
  `c((−1)^{r+1}) · realAdjacentGodementCoefficient D (−a) (realRectangularSchwartzFourier a Φ) Ũ c⁻¹ g`.
  The proof evaluates the Library's `realGodementColumnReflection` at `w_{r+2} g`.
* `rotatedValue t q a D' c F T U` is the right translate by `tailWeyl k (q+2)` of the Godement coefficient
  `realAdjacentGodementCoefficient D' a (realColumnProduct F (T.tail_{q+1})) U c`. The private lemma
  `dual_rotatedValue` shows that its dual, at `g · unfoldingWeyl`, is the dual of the unrotated
  coefficient at `g`: inverse transpose fixes the tail Weyl element, which is an involution.

`RealGapExactRestrictionStatement` (proved by `realGapExactRestriction`): with `a`, `D'`, `η₁`, `κ`, `μ`,
`σ`, `η` as in `RealGapNormalizedRestrictionStatement` and `ρ = σ × (rectangularMeasure μ q k × η)`, there
is `C > 0` such that for all `ds`, `dds`, `c`, every Schwartz `F = squareEval T`, every
`U ∈ realUniformWhittakerModel (t+1+q) ds (−a)` whose dual lies in
`realUniformWhittakerModel (t+1+q) dds a`, and every `g ∈ GL_{t+1}(ℝ)`, with `W = rotatedValue …`:

1. the ordinary fiber integral is integrable for `σ` and
   `W(diag(g, 1)) = η_c(det w_{q+2}) · realAdjacentWeylSign (t+1+q) c · P g (1/2) · C · ∫∫ unitOrdinaryKernel`;
2. for every lower rectangle `X`, the dual kernel `unitDualKernel a c F T Ũ g (rectangleRows X)` is
   integrable for `ρ` and
   `dualFunction W (rectangularPoint g X · unfoldingWeyl) =
   c((−1)^n) · realAdjacentWeylSign (t+1+q) c⁻¹ · P g (1/2) · C · ∫ unitDualKernel …`.

The proof combines `realGapNormalizedRestriction` with the coordinates of `RealGapRankCoordinates`.
The separated test `realColumnProduct F (T.tail_{q+1})` satisfies the separation hypothesis by
`realColumnProduct_joinLastColumn`, and its transform is `realColumnProduct F̂ f̂` by
`RealJacquet.realColumnProduct_fourier`. Dual model membership of `Ũ` is a hypothesis, as in the
Library's `RealJacquet.RealAdjacentGodementUnfoldingStatement`. The formula displays the reflection
factor `c((−1)^n)` and the two Weyl determinants of `realAdjacentWeylSign (t+1+q) c⁻¹` separately. Since
`det(w_{n+1}) det(w_n) = (−1)^n` (`determinant_weylLong_succ` and `det(w_n)² = 1`), their dual character
factor is `c((−1)^n)^{-1}`, so the displayed product equals one. The ordinary identity is the
alternate restriction of Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.2, (10.6), p. 73;
the dual identity is the reflected restriction and the change to the dual chart of §10.3,
(10.7)–(10.9), pp. 75–76.
