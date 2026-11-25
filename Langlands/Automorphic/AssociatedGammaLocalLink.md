# The gamma factor of a finite pair factor choice

Supporting module for the proof of `AssociatedGammaStatement` (module `Langlands.Automorphic.AssociatedGammaLocalLink`), glue step linking the local factors used in the
comparison engine to the actual automorphic pair gamma factor. This supplies the
`IsAutomorphicPairGammaFactor` and `HasRationalContinuation` conjuncts of
`HasHeckeGammaCertificate` (module `Langlands.Automorphic.AssociatedGammaHeckeReduction`).

## Polynomial lemmas (namespace `Langlands.RankinSelberg`)

- `eval_spectralPoint_ne_zero_of_coeff`: if `P.coeff 0 ≠ 0` and `q > 1`, then
  `P(q^(-s)) ≠ 0` on a right half-plane. `P` is nonzero on a ball around `0`, and
  `‖q^(-s)‖ = q^(-re s)` is small for large `re s`.
- `eval_spectralPoint_ne_zero_of_ne_zero`: the same for every nonzero `P`. Write
  `P = X^k Q` with `X ∤ Q` (`exists_eq_pow_rootMultiplicity_mul_and_not_dvd` at `0`); then
  `Q.coeff 0 ≠ 0`, and `q^(-s) ≠ 0`.
- `eval_spectralPoint_one_sub_ne_zero`: for nonzero `P`, `P(q^(-(1-s))) ≠ 0` on a right
  half-plane. Every root of `P` has norm at most `M - 1`, where `M` is the sum of the norms of
  the distinct roots plus `1`. Also `‖q^(-(1-s))‖ = q^(re s - 1) > M` once
  `re s > 1 + log_q M`.
- `hasRationalContinuation_polynomialGammaExpression`: for `δ = q⁻¹` and `Pd ≠ 0`, the
  published `polynomialGammaExpression q c m P Pd` (`c q^(-ms) Pd(q^(-(1-s)))⁻¹ / P(q^(-s))⁻¹`)
  has rational continuation `rationalGammaExpression δ c m P Pd`. Take a half-plane on which
  the reduced denominator of the rational function does not vanish at `q^(-s)` (second lemma)
  and on which `Pd(q^(-(1-s))) ≠ 0` (third lemma). Then evaluate with the published
  `eval_rationalGammaExpression` and `spectralPoint_one_sub`.

## The finite pair factor choice (namespace `…CuspidalPairFunctionalEquation.FinitePairFactorChoice`)

- `localFactors c v`: the `LocalFactors` `(c.finiteL v, c.finiteDualL v, c.finiteEpsilon v)`.
- `rationalGamma c v`: `rationalGammaExpression (residueReflection (padicField v)) c_v m_v P_v Pd_v`
  from the chosen epsilon `(c_v, m_v)` and L-polynomials.
- `localFactors_gamma`: `(c.localFactors v).gamma` is the polynomial gamma expression of
  these data (definitional).
- `dualLPolynomial_ne_zero`: the chosen dual L-polynomial is nonzero
  (`IsLanglandsPairLPolynomial.ne_zero`).
- `hasRationalContinuation_gamma`: `(c.localFactors v).gamma` has rational continuation
  `c.rationalGamma v` (`coe_residueReflection` gives `δ = q_v⁻¹`).
- `isAutomorphicPairGammaFactor`: if the local classes of `Pd`, `Pd'` at `v` are the smooth
  duals of those of `P`, `P'`, then `c.rationalGamma v` is an automorphic pair gamma factor of
  the local classes of `P`, `P'` at `v`, for `c.additive v` and `c.measure v`. The witnesses
  are the dual classes, `c.lPolynomial_spec v`, `c.dualLPolynomial_spec v` and
  `c.epsilon_spec v`.
