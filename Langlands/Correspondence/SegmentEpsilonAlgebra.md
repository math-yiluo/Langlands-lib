# Rational-function algebra for segment-pair epsilon factors

Author: Worker 1695.

This module contains elementary algebra in `RatFunc K` used to compare gamma
factors of segment pairs. All results are proved unconditionally, with only the
standard axioms.

## Evaluation (namespace `Langlands.RankinSelberg.RationalEvaluation`)

`RegularAt R z` is the published condition that the reduced denominator of `R`
does not vanish at `z`.

- `RegularAt.prod`, `eval_prod`: a finite product of rational functions regular
  at `z` is regular at `z`, and its value is the product of the values (induction
  on the finset, using `RegularAt.mul` and `eval_mul`).
- `regularAt_rationalLRatio`, `eval_rationalLRatio`: for a Weil–Deligne pair `A`,
  a normal subgroup `I`, `g : G`, a unit `c` and a point `z ≠ 0` such that the
  dual Euler polynomial does not vanish at `c / z`, the reflected L-ratio
  `rationalLRatio A I g c` is regular at `z`. Its value there is
  `P_A(z) / P_(A^∨)(c / z)`. The proof uses the published formula
  `rationalLRatio_eq`.

## Monomials and cancellation (namespace `Langlands.RankinSelberg`)

- `subst_monomial c a m`: under the reflection `X ↦ c / X`,
  `a X^m ↦ (a c^m) X^(-m)`.
- `monomial_mul_cancel`: suppose `a X^m P = b X^n P'` in `RatFunc K` with
  `a, b ≠ 0` and `P(0) = P'(0) = 1`. Then `m = n` and `a = b`. Proof: with
  `m ≤ n`, cancel `X^m` and compare constant coefficients of the polynomial
  identity `a P = b X^(n-m) P'`. The case `n < m` is symmetric.
- `prod_X_zpow`, `prod_rationalEpsilonMonomial`: a double product of epsilon
  monomials `c_ij X^(m_ij)` is the epsilon monomial of
  `epsilonFactorProduct`, that is `(∏ c_ij) X^(Σ m_ij)`.
- `rationalGammaExpression_cancel`: suppose
  `rationalGammaExpression δ c m P D = rationalGammaExpression δ c' m' P D'`,
  that is `c X^m P / D(δ/X) = c' X^(m') P / D'(δ/X)`, with `P ≠ 0` and
  `D(0) = D'(0) = 1`. Then `c = c'` and `m = m'`. The proof has four steps:
  1. Cancel `P` and cross-multiply.
  2. Apply the involution `RationalReflection.subst δ`, which takes `D(δ/X)` back
     to `D`.
  3. Rewrite the monomials by `subst_monomial`.
  4. Apply `monomial_mul_cancel`, then cancel `δ^m`.

## Provenance

Derived algebra; no literature claim is made. The cancellation lemma is the
algebraic step that identifies two epsilon monomials from equal gamma
expressions. It uses only that the dual L-polynomials have constant term `1`.
