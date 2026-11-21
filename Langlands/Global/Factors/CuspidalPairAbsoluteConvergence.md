# Absolute convergence of cuspidal pair Euler products

`Langlands.Global.cuspidalPairAbsoluteConvergence` proves
`Langlands.Global.CuspidalPairAbsoluteConvergenceStatement.{u, uQ}`. The
statement applies to actual cuspidal realizations with unitary central
characters and spectral presentations over a number field with compact adele
quotient. For every finite set of finite places containing both exceptional
sets and every complex `s` with `1 < s.re`, it gives

1. summability of the norms of the logarithmic Euler terms indexed by pairs
   of a place outside the finite set and a natural number,
2. summability of the norms of the corresponding Euler factors minus one,
3. unconditional convergence of the product of those factors to the complex
   exponential of the sum of the logarithmic Euler terms.

## Proof

The theorem applies `cuspidalPairAbsoluteConvergenceReduction.{u, uQ}` to
`cuspidalSelfPairContinuation.{u, uQ}`.
The reduction takes holomorphic continuation of the self-pair partial Euler
product to `Re s > 1` as its premise. It uses the local logarithmic expansion
and Landau's theorem for the nonnegative self-pair coefficients, then passes
to general pairs by Cauchy–Schwarz and exponentiates the summable logarithmic
series. The imported continuation theorem supplies the premise at the same
universes. [Reduction proof](CuspidalPairAbsoluteConvergenceProof.md),
[continuation proof](CuspidalSelfPairContinuationProof.md).

## Source

H. Jacquet and J. A. Shalika, *On Euler products and the classification of
automorphic representations I*, Amer. J. Math. 103 (1981), 499–558. Lemma
(5.2) is on pp. 554–555 (PDF pp. 56–57). Theorem (5.3) is on p. 555
(PDF p. 57), and its proof uses (5.2) on p. 556 (PDF p. 58) within the
argument on pp. 555–557 (PDF pp. 57–59). The double series and exponential
form of the product come from (5.3.2) and (5.3.5) in that proof.

Registered source
`provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`,
SHA256 `c6b669ccf00a3ce35c10aa60f3dc7538d6269bf279791e5286b893c597275620`.
