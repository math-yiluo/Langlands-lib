# Symmetric polynomial two-cocycles of the additive group

Worker 716. Internal lemma for the proof of
`Langlands.GroupScheme.PerfectFieldOneDimensionalUnipotentStatement`. It is a
polynomial, perfect-field form of the classical description of symmetric
two-cocycles of the additive group. No registered source was used. The argument
below is self-contained and is the one implemented in Lean.

## Conventions

A two-variable polynomial is an element `c` of `k[X][X]`. The inner variable
is written `X` and the outer variable `Y`, so `c = ∑ⱼ cⱼ(X) Yʲ`.

- `ev2 u v c` evaluates `c` at `X = u`, `Y = v` in any `k`-algebra. It is a
  `k`-algebra homomorphism. `comp_ev2` says it commutes with algebra maps.
- `shift h` is `h(X + Y)`.
- `coboundary f` is `f(X + Y) - f(X) - f(Y)`.
- `defect c` is `c(X+Y, Z) + c(X, Y) - c(X, Y+Z) - c(Y, Z)` in `k[X][Y][Z]`,
  built from the three variables `varU`, `varV` and `varW`. `IsCocycle c`
  means `defect c = 0`.
- `powerSum p c` is `∑_{i<p} c(i X, X)` in `k[X]`.

`Bivariate.swap` (Mathlib) exchanges `X` and `Y`. "Symmetric" means
`Bivariate.swap c = c`, and "normalized" means `c.coeff 0 = 0`, i.e. `c(X, 0) = 0`.

## Main results

- `exists_eq_coboundary_of_charZero`: if `k` has characteristic zero and `c`
  is a normalized cocycle, then `c = coboundary f` for some `f : k[X]`.
- `exists_eq_coboundary_of_charP p`: let `k` be perfect of prime
  characteristic `p`. If `c` is a symmetric normalized cocycle with
  `powerSum p c = 0`, then `c = coboundary f` for some `f`. The Lean statement
  is quantified over a bound `N ≥ natDegree c`, so that it can be proved by
  strong induction on `N`.

## Implemented argument

**The derivative identity** (`derivative_eq_of_isCocycle`). Let `g = c.coeff 1`.
This is the coefficient of `Y`, so `g(X) = ∂_Y c(X, 0)`. The lemmas `ev2_U_V`,
`ev2_U_VW`, `ev2_UV_W` and `ev2_V_W` write the four terms of the defect in
closed form. Taking the coefficient of `Z¹` in `defect c = 0` gives

`∂_Y c(X, Y) = g(X + Y) - g(Y)`.

Lemma `derivative_coboundary` gives the same identity for coboundaries, with
`g = f'`.

**Characteristic zero.** `exists_antiderivative` produces `G` with `G' = g` and
`G(0) = 0`. Then `c - coboundary G` has `Y`-derivative zero, so it is constant
in `Y`. Its `Y⁰` coefficient is `c(X, 0) + G(0) = 0`, so the difference is zero.

**Characteristic `p`.** The induction step goes as follows.

1. *The obstruction kills the coefficient of `X^{p-1}` in `g`.*
   `coeff_powerSum` computes the coefficient of `X^p` in `powerSum p c` as
   `-(g.coeff (p-1))`. It uses the power sums `∑_{i<p} iᵐ` in `k`.
   `sum_range_pow_eq_zero` shows these vanish for `m < p - 1`, and
   `sum_range_pow_sub_one` shows the sum is `-1` for `m = p - 1`. Both are
   proved through `ZMod p` and `FiniteField.sum_pow_lt_card_sub_one`.
   Normalization removes the remaining term.
2. *Lucas's theorem kills the coefficients of `g` in degrees `n ≡ -1 (mod p)`
   with `n ≥ p`.* The coefficient of `Y^{p-1}` in `∂_Y c` is `p · c_p = 0`.
   In `g(X + Y) - g(Y)`, the coefficient of `X^{n-(p-1)} Y^{p-1}` is
   `choose n (p-1) · gₙ`. Lucas's theorem
   (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`) gives
   `choose n (p-1) ≡ 1 (mod p)` for these `n`.
3. Together, steps 1 and 2 show that `g.coeff n = 0` whenever `n + 1 = 0` in `k`.
   So `exists_antiderivative` gives `G` with `G' = g`, `G(0) = 0` and
   `deg G ≤ deg g + 1`. The difference `c₁ = c - coboundary G` is again a
   symmetric normalized cocycle with vanishing obstruction:
   `powerSum_coboundary` telescopes the obstruction of a coboundary to zero.
   Its `Y`-derivative is zero, and `natDegree c₁ ≤ N`.
4. Vanishing of `∂_Y c₁` shows that only powers `Y^{pj}` occur in `c₁`. By
   symmetry (`coeff_coeff_swap`), only powers `X^{pi}` occur. Every coefficient
   has a `p`-th root because `k` is perfect, so `exists_pow_eq_of_coeff`
   (applied twice) gives `c₁ = c₄^p`.
5. The Frobenius identities `defect_pow`, `powerSum_pow` and `coboundary_pow`
   and injectivity of Frobenius show that `c₄` is a symmetric normalized
   cocycle with vanishing obstruction and `natDegree c₄ < N`. By induction,
   `c₄ = coboundary F`, and then `c = coboundary (F^p + G)`.

The base case `N = 0` holds because a normalized polynomial of `Y`-degree zero
is zero.
