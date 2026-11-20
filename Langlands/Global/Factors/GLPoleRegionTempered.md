# The essentially tempered case of the GL pole-region statement

This internal module supports the proof `Langlands.Global.glPairPoleRegion` of
`Langlands.Global.GLPairPoleRegionStatement`. It proves the essentially tempered
case of Henniart (1986), Proposition 4.5(ii), `GL_n` side, in both equal and
unequal rank. Henniart's argument (§4.8, printed pp.162–163) is summarized in
`GLPoleRegionStatement.md`.

## Statement

`Langlands.Global.GLPoleRegion.hasNoReflectedCommonZero_of_essentiallyTempered`
works over the canonical realization `F.canonicalTopologicalData`, with residue
cardinality `q`. Its data are:

- a self-dual Haar measure `ν` for `ψ`, and a self-dual Haar measure `νd` for
  `ψ⁻¹ = ψ.scale (-1)`;
- ranks `t ≤ r`;
- irreducible representations `π` of `GL_(r+1)(F)` and `σ` of `GL_(t+1)(F)`, both
  essentially tempered (`IsEssentiallyTempered`);
- `P` with `IsPadicPairLPolynomial F ψ ν.val π σ P`;
- `Pdual` with `IsPadicPairLPolynomial F (ψ.scale (-1)) νd.val π^ι σ^ι Pdual`,
  where `π^ι` is `inverseTransposePullback π`.

It concludes `HasNoReflectedCommonZero q P Pdual`.

## Proof

1. Essential temperedness gives real `a`, `b` such that `|det|^(-a) π` and
   `|det|^(-b) σ` are tempered (`realPowerTwist` by the published
   `determinantNorm`). Write `π = |det|^a π₀` and `σ = |det|^b σ₀` with `π₀`, `σ₀`
   tempered (`realPowerTwist_cancel_neg`, `realPowerTwist_neg_cancel`). Twisting
   preserves irreducibility (`isIrreducible_twist_iff`).
2. Since `t ≤ r`, the pair relation is the symmetric relation
   (`isPadicSymmetricLPolynomial_of_le`). The published
   `analyticTemperedTwistLPolynomial_poleFree` gives `P(z) ≠ 0` for
   `‖z‖ < q^(a+b)`.
3. On the dual side the following hold:
   - `π₀^ι` and `σ₀^ι` are irreducible
     (`CuspidalSupport.isIrreducible_comp_of_surjective`, for the inverse
     transpose).
   - They are tempered (`isTempered_comp_continuousMulEquiv` with
     `generalLinearInverseTranspose`).
   - `(|det|^a π₀)^ι = |det|^(-a) π₀^ι`, by the published
     `inverseTransposePullback_realPowerTwist`.

   So `Pdual` is the symmetric L-polynomial of `|det|^(-a) π₀^ι × |det|^(-b) σ₀^ι`
   for `ψ.scale (-1)`. The same theorem gives `Pdual(w) ≠ 0` for
   `‖w‖ < q^(-a-b)`.
4. `hasNoReflectedCommonZero_of_radii` (from `GLPoleRegionTransport`) applies
   with `R = q^(a+b)` and `R' = q^(-a-b)`, because `q R R' = q > 1`.

This is the zero-free-disk argument of Henniart §4.8. The Library theorem
`analyticTemperedTwistLPolynomial_poleFree` supplies the bound on tempered poles.
In Henniart's argument that bound comes from his §2.6.

## Dependencies

The module imports `Langlands.Global.Factors.GLPoleRegionTransport` (this
submission) and the published modules
`RankinSelberg/AnalyticTemperedTwistLPolynomialData`,
`RankinSelberg/CenteredBlockLPolynomialProof`,
`Classification/InverseTransposeAnalyticProof`,
`CuspidalSupport/CuspidalTensorAssociationProof` and `Twist/SubquotientProof`.
It introduces no axioms and no hypotheses.
