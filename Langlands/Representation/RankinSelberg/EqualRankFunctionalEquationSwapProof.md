# Equal-rank epsilon and gamma exchange: proof

The theorem `Langlands.RankinSelberg.equalRankFunctionalEquationSwap` proves
the closed proposition
`Langlands.RankinSelberg.EqualRankFunctionalEquationSwapStatement` in the
three independent universes `uF`, `uV` and `uW`. Its type is exactly
`EqualRankFunctionalEquationSwapStatement.{uF, uV, uW}`; the statement module
and everything it imports are unchanged.

## Proof

The proof is a projection. It introduces the statement's outer parameters
in their original order: the prime `p` with its `Fact p.Prime` instance, the
field `F : PadicField.{uF} p`, the additive character `ψ`, the supplied
self-dual Haar measure `ν`, the rank parameter `n`, the carriers `V` and `W`
with their additive group and complex module instances, the representations
`π` and `σ`, and the two hypotheses that `π` and `σ` are of Whittaker type
for `standardCharacter ψ n`.

It then applies the published theorem
`Langlands.RankinSelberg.equalRankFactorSwap :
EqualRankFactorSwapStatement.{uF, uV, uW}` from module
`Langlands.Representation.RankinSelberg.EqualRankFactorSwapProof` to the same
arguments. That proposition has the identical binder prefix and concludes the
conjunction of the L-polynomial, epsilon and gamma certificate equivalences.
The proof takes the second component, which is the epsilon/gamma conjunction:

- for every `e : ℂˣ × ℤ`, `IsPadicPairEpsilonFactor F ψ ν.val π σ e` holds
  if and only if `IsPadicPairEpsilonFactor F ψ ν.val σ π e` does;
- for every `G : RationalFunctions`,
  `IsPadicPairGammaFactor F ψ ν.val π σ G` holds if and only if
  `IsPadicPairGammaFactor F ψ ν.val σ π G` does.

Both sides use the original character `ψ` and the same Haar measure
`ν.val`. The L-polynomial conjunct is discarded. No new lemma, hypothesis or
construction is introduced. The kernel check reports only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## What the imported proof establishes

All mathematical content comes from the published full exchange proof
(accepted proof artifact `70e11a12-5c7e-4fe0-a6e2-a57bd2de2407`) and its
supporting `EqualRankSwapFactors` module. As its Markdown records, the
epsilon and gamma transports work as follows. They translate both Whittaker
functionals by the minus-one diagonal matrix, exchange them, and keep the
actual row Fourier pair at the original character and the supplied Haar
measure. They convert the second model's minus-one scalar, and they keep
every compatible quotient measure, nonzero-functional test, rational
continuation and normalized generator.

Nothing is added to the imported factor relations or to the statement's
hypotheses. There is no irreducibility, analytic or factor-existence premise,
and no claim that an epsilon or gamma factor exists. The inverse-transpose
dual pullbacks on the original carriers are not identified with smooth
contragredients.

## Provenance

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464. It is registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Section 2.12, printed page 403 (PDF 38), states equal-rank epsilon symmetry.
Gamma symmetry is derived content: Section 3.1(2), printed page 404 (PDF 39),
gives the ratio formula relating gamma to epsilon and L-factors. The formal
proof here does not follow that ratio route. It cites the published full
exchange theorem as its only proof source.
