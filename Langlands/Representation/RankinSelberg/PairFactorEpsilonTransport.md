# Fixed-functional transport of the unequal-rank epsilon equation

Lean module: `Langlands.Representation.RankinSelberg.PairFactorEpsilonTransport`.

This module proves the analytic core of the epsilon half of
`Langlands.RankinSelberg.PairFactorCharacterChangeStatement`. Fix the
functionals. Then the fixed-monomial unequal-rank functional equation
(`UnequalRankEpsilonEquation`) for an additive character `ψ` gives the one for
`ψ^a(x) = ψ(a x)`. This is the change of variables in the proof of Cogdell and
Piatetski-Shapiro 1994, Lemma 2.1 (printed pages 161–163). The block-by-block
reduction, the explicit constants and the treatment of the central characters
were worked out for this formalization. The matrix and integral identities it
uses come from `UnequalRankDualCharacterChange`. The monomial bookkeeping
comes from `PairFactorCharacterChangeAlgebra`.

## Relation to the printed constants

The printed lemma is for `GL_n × GL_m` with `m < n` and fixed Haar measures,
where the paper's `(n, m)` is `(r+1, n+1)` here, so `N = nm`. It gives
`ε(s, ψ^λ) = ω_Π(λ)^m ω_τ(λ)^n |λ|^(nms - d) ε(s, ψ)` with
`d = nm - m(m+1)/2`. The printed computation uses the original integral with no
rectangular variable (block `j = 0`) and the dual integral with
`k = n - m - 1` rectangular rows (paper's `n`, `m`).

Changing `ψ` to `ψ^a` replaces the self-dual measure `ν` by `ν₂ = κ ν`, with
`κ = |a|^(1/2)`. A rectangular product measure with `t` rows and `m` columns is
then scaled by `κ^(tm)` (`rectangularMeasure_eq_smul`). In block `j = 0` only
the dual side has a rectangular variable, so the epsilon factor gains
`κ^(km) = |a|^(km/2)`. Since `-d + km/2 = -nm/2`, the self-dual version of the
printed change is `ω_Π(a)^m ω_τ(a)^n |a|^(nm(s - 1/2))`. In this module's
notation that is `ω_π(a)^(n+1) ω_σ(a)^(r+1) |a|^(N(s - 1/2))`. For the epsilon
monomial `c X(s)^e` this means the coefficient is multiplied by
`ω_π(a)^(n+1) ω_σ(a)^(r+1) |a|^(-N/2)` and the exponent is shifted,
`e ↦ e + N ord a`, because `|a|^(Ns) = X(s)^(N ord a)`.

The proof below does not use the printed constants `A`, `B`, `C`, `D` or `d`.
It computes the constants of every block `(j, k)` with `j + k + 1 = r - n`
directly, including the measure factors `κ^(j(n+1))` and `κ^(k(n+1))`.

## Notation

`n < r`. `π` acts on `V` through `GL_(r+1)(F)` and `σ` on `W` through
`GL_(n+1)(F)`. `d_a = characterChangeElement a m = diag(a^m, ..., a, 1)`.
`R = blockCorrectionAt a n r`, and `ℓ_a`, `ℓ'_a` are the translated functionals
`characterChangeFunctional ψ π a ℓ` and `characterChangeInverseFunctional ψ σ a ℓ'`.
`X(s)^e` stands for `spectralPoint q s ^ e`, with `spectralPoint q s = q^(-s)`.
`U(n, j, k)` is the Library unit `unequalRankCharacterChangeScalar abv a n j k`.
`N = (r+1)(n+1)` and `S = ∑_{i ≤ n} (n - i)`, so `|det d_a| = |a|^S`.

## Transfer

- `UnequalRankEpsilonEquation.transfer`: start from
  `UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ ℓ ℓ' c m`, with `q > 0`.
  Assume:
  - every minus-one scalar `ζ` of `ℓ'` is one of `ℓ₂'`;
  - `T : V → V` is surjective;
  - for every block `(j, k)` with `r = n + (j + k + 1)` there are units `α`, `β`
    and integers `A`, `B` with `m' + A = m - B` and `c' α = c β q^(-B)`;
  - for these, the original integral of block `(j, k)` for `ψ₂`, `ν₂`, `ℓ₂`,
    `ℓ₂'` at the model functions of `v` and `u` is `α X(s)^A` times the integral
    for `ψ`, `ν`, `ℓ`, `ℓ'` at the model functions of `T v` and `u`;
  - the dual integrals (`dualUnequalRankModelIntegralAt`) satisfy the same
    relation with `β X(s)^B`.

  Then `UnequalRankEpsilonEquation hnr q ψ₂ abv μ ν₂ π σ ℓ₂ ℓ₂' c' m'` holds.
  Proof: keep the minus-one scalar `ζ` and the generators `P` and `Pdual`. The
  Laurent spans of the original and the dual value sets are unchanged by
  `zetaSpan_values_eq_of_monomial` (with `unequalRankValuesAt_eq` for the
  original family), so `P` and `Pdual` are still the normalized generators. The
  functional equations transfer by `functionalEquation_transfer_of_monomial`.
  Both lemmas use the surjectivity of `modelMap`.

## Minus-one scalar

- `HasModelMinusOneScalar.characterChange`: if `ℓ'` has minus-one scalar `ζ`,
  so does `ℓ'_a`. The model function of `u` for `ℓ'_a` is the left translate by
  `d_a` of the one for `ℓ'`, and `d_a (-g) = -(d_a g)`.

## Blocks

Hypotheses common to both block lemmas: `ν₂ = κ • ν` with `ν` σ-finite, the
quotient measure `μ` has the character-change law
(`HasCharacterChangeMeasureLaw abv a μ`), and `|det d_a| = q^(-e)` for the rank
`n + 1`.

- `forwardBlock_characterChange`: assume also the rectangular law
  `HasCharacterChangeRectangularMeasureLaw abv a j n` for the product measure of
  `ν` with `j` rows. Then the original integral of block `(j, k)` for `ψ^a`, `ν₂`
  at the model functions of `v` for `ℓ_a` and `u` for `ℓ'_a` equals
  `κ^(j(n+1)) U(n, j, k) X(s)^(-e)` times the integral for `ψ`, `ν` at the model
  functions of `π(R) v` for `ℓ` and `u` for `ℓ'`. Proof: the model-function
  identities, the scaling `rectangularMeasure_eq_smul`
  (`unequalRankIntegralAt_congr_smul`), and `unequalRankIntegralAt_characterChange`.

- `dualBlock_characterChange`: let `ω_π` and `ω_σ` be central characters of `π`
  and `σ`. Assume also that `μ` is right invariant, that the product measure of
  `ν` with `k` rows has the rectangular character-change law, and that it scales
  by `determinantWeight abv g (-k)` under right multiplication by every `g` in
  `GL_(n+1)(F)`. Then the dual integral of block `(j, k)` for `ψ^a`, `ν₂`, `ℓ_a`,
  `ℓ'_a` at `(v, u)` equals

  `κ^(k(n+1)) ω_π(a)^(n+1) ω_σ(a)^n U(n, k, j) ω_σ(a^(r-n+1)) · X(s)^(-e) · determinantWeight abv (a^(r-n+1) I_(n+1)) ((k+j+1)/2 - s - k)`

  times the dual integral for `ψ`, `ν`, `ℓ`, `ℓ'` at the model functions of
  `π(R) v` and `u`. Proof, with `E = diag(a^(-(r-n+1)) I_(n+1), I_(r-n))` and
  `g = a^(-(r-n+1)) I_(n+1)`:
  1. By `firstDual_modelMap_characterChangeFunctional`,
     `secondDual_modelMap_characterChangeInverseFunctional`, the measure scaling
     and `(ψ^(-1))^a = (ψ^a)^(-1)`, the integral equals
     `κ^(k(n+1)) ω_π(a)^(n+1) ω_σ(a)^n` times the integral of block `(k, j)` for
     `ψ^(-1)` of the corrected first dual function of `π(E) π(R) v` and the left
     translate by `d_a` of the second dual function of `u`.
  2. The forward change of character `unequalRankIntegralAt_characterChange` for
     `ψ^(-1)` in block `(k, j)` gives the factor `U(n, k, j) X(s)^(-e)`.
  3. The translation law `dualIntegralAt_translate'` for `g`, where
     `ι g = a^(r-n+1) I_(n+1)`, replaces `π(E) π(R) v` and `u` by `π(R) v` and
     `σ(g⁻¹) u`. This gives the determinant weight.
  4. `σ(g⁻¹) u = ω_σ(a^(r-n+1)) u` by the central character of `σ`.

## Constants

- `ofReal_cpow_eq_exp`, `ofReal_pow_eq_exp`: for `x > 0`, `x^z = exp(log x · z)`
  and `x^m = exp(log x · m)` in `ℂ`.
- `sum_fin_sub_mul_two`: `2 ∑_{i ≤ n} (n - i) = n(n+1)`.
  `sum_fin_succ_mul_two`: `2 ∑_{i < j} (i + 1) = j(j+1)`.
- `abv_det_characterChangeElement`: `|det d_a| = |a|^S`.
  `abv_det_scalar`: `|det(b I_m)| = |b|^m`.
- `abv_det_characterChangeElement_eq_zpow` and `abv_det_scalar_pow_eq_zpow`:
  if `|a| = q^(-o)`, then `|det d_a| = q^(-oS)` and
  `|det(a^t I_m)| = q^(-o t m)`.
- `determinantWeight_sub_eq`: if `|det g| = q^(-e)` and `q > 0`, then
  `determinantWeight abv g (t - s) = determinantWeight abv g t · X(s)^(-e)`.
- `blockConstants_eq`: assume `|a| = q^(-o)`, `κ^2 = |a|` and
  `r = n + (j + k + 1)`. Then for all complex `c`, `w_π`, `w_σ`:

  `c w_π^(n+1) w_σ^(r+1) |a|^(-N/2) · κ^(j(n+1)) U(n, j, k) = c · κ^(k(n+1)) w_π^(n+1) w_σ^n U(n, k, j) w_σ^(r-n+1) · determinantWeight abv (a^(r-n+1) I_(n+1)) ((k+j+1)/2 - k) · q^(-B)`

  with `B = -oS - o(r-n+1)(n+1)`. Proof: every positive real factor is written as
  `exp(log · ...)`. The exponent identity is then a polynomial identity in
  `log q`. It is proved by `linear_combination` from `2S = n(n+1)`,
  `2∑_{i<j}(i+1) = j(j+1)`, `2∑_{i<k}(i+1) = k(k+1)`, `log κ = log|a|/2` and
  `log|a| = -o log q`.

## Generic transport

- `UnequalRankEpsilonEquation.characterChange`: assume the following.
  - `q > 0` and `|a| = q^(-o)`.
  - `μ` has the character-change law and is right invariant.
  - `ν` is σ-finite, `ν₂ = κ • ν` and `κ^2 = |a|`.
  - For every `t`, the product measure of `ν` with `t` rows has the rectangular
    character-change law and the right-scaling law
    `∫ G(x g) = determinantWeight abv g (-t) ∫ G`.
  - `ω_π` and `ω_σ` are central characters of `π` and `σ`.
  - `c' = c ω_π(a)^(n+1) ω_σ(a)^(r+1) |a|^(-N/2)`.

  Then `UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ ℓ ℓ' c m` implies
  `UnequalRankEpsilonEquation hnr q (ψ.scale a) abv μ ν₂ π σ ℓ_a ℓ'_a c' (m + N o)`.
  The measure laws are hypotheses here; the p-adic module
  `PairFactorCharacterChangeProof` supplies them. Proof: apply `transfer` with
  `T = π(R)`, which is surjective because `R` is invertible. The minus-one
  scalar is preserved by `HasModelMinusOneScalar.characterChange`, with
  `e = oS` (`abv_det_characterChangeElement_eq_zpow`). In block `(j, k)`, take:
  - `α = κ^(j(n+1)) U(n, j, k)` and `A = -oS` (`forwardBlock_characterChange`);
  - `β = κ^(k(n+1)) ω_π(a)^(n+1) ω_σ(a)^n U(n, k, j) ω_σ(a^(r-n+1)) · determinantWeight abv (a^(r-n+1) I) ((k+j+1)/2 - k)`;
  - `B = -oS - o(r-n+1)(n+1)` (`dualBlock_characterChange`, with the spectral
    part split off by `determinantWeight_sub_eq`).

  The exponent condition `m + N o + A = m - B` follows from `2S = n(n+1)` and
  `r = n + (j + k + 1)`. The coefficient condition is `blockConstants_eq`.
