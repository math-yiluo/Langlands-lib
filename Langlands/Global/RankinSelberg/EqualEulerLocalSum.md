# The local unramified sum of the equal-rank Whittaker integral

Module `Langlands.Global.RankinSelberg.EqualEulerLocalSum`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualEulerLocal`.

## Content

Fix `n` and two tuples `a, b : Fin (n + 1) → ℂˣ` of Satake parameters. Write `s_λ(a)` for
the Library's Schur value `satakeSchur a λ` (the Jacobi–Trudi value of `λ - λ_n`, times
`(∏ a_i) ^ λ_n`). `halfModulus q λ` is `δ_B^(1/2)(ϖ^λ) = q^(-(∑_i (n - 2i) λ_i)/2)`, and
`spectralPoint q s = q ^ (-s)`.

### The local term and its sum

- `pairGrowth a b = (1 + ∑ ‖a_i‖) ^ (n + 1) * (1 + ∑ ‖b_j‖) ^ (n + 1)`, an explicit rate.
- `equalRankLocalTerm a b t λ`, for `λ : Fin (n + 1) → ℤ`, is
  `s_λ(a) s_λ(b) t ^ |λ|` when `λ` is antitone (dominant) and `λ_n ≥ 0`, and `0`
  otherwise. Here `|λ| = ∑ λ_i`, which is `≥ 0` on those weights and is used through
  `Int.toNat`.
- `hasSum_equalRankLocalTerm a b t`: if `pairGrowth a b * ‖t‖ < 1`, then
  `HasSum (equalRankLocalTerm a b t) (∏_i ∏_j (1 - a_i b_j t))⁻¹`.
  `summable_norm_equalRankLocalTerm` gives absolute summability under the same hypothesis.
- Auxiliary: `norm_jacobiTrudiValue_le_rate`, `norm_le_completeGrowthRate_pow`,
  `summable_and_tsum_schurPairTerm` (the same statement indexed by antitone natural
  weights, with the Library's `schurPairTerm`), `natWeight`, `natWeight_injective`,
  `equalRankLocalTerm_natWeight`, `equalRankLocalTerm_eq_zero`.

### A radius uniform in the residue cardinality

- `localRadius n C C' = (n + 1) (2 (n + 1) + max C 0 + max C' 0)`.
- `succ_succ_le_two_pow n : n + 2 ≤ 2 ^ (n + 1)` (auxiliary).
- `completeGrowthRate_le_rpow`: if `q ≥ 2` and `‖x_i‖ ≤ q ^ C` for all `i`, then
  `1 + ∑ ‖x_i‖ ≤ q ^ ((n + 1) + max C 0)`.
- `pairGrowth_le_rpow`: if `q ≥ 2`, `‖a_i‖ ≤ q ^ C` and `‖b_j‖ ≤ q ^ C'`, then
  `pairGrowth a b ≤ q ^ localRadius n C C'`.
- `pairGrowth_mul_norm_spectralPoint_lt`: for a natural number `q ≥ 2` and the same
  bounds, `localRadius n C C' < Re s` implies `pairGrowth a b * ‖q ^ (-s)‖ < 1`. The
  threshold does not depend on `q`, so one half-plane works at every place.

### The unramified pair Euler factor

- `mem_ofTuple a i`: `a_i` belongs to the multiset `Eigenvalues.ofTuple a`.
- `eval_pairEulerPolynomial_ofTuple a b t`: the Library's pair Euler polynomial of
  `ofTuple a` and `ofTuple b`, evaluated at `t`, is `∏_i ∏_j (1 - a_i b_j t)`.
- `hasSum_equalRankLocalTerm_eulerFactor`: let `A, B : Eigenvalues (n + 1)` be
  enumerated by `a`, `b` (`ofTuple a = A`, `ofTuple b = B`), with every element of `A`
  bounded by `q ^ C` and every element of `B` by `q ^ C'`, where `q ≥ 2`. If
  `localRadius n C C' < Re s`, then the terms `equalRankLocalTerm a b (q ^ (-s))` sum to
  `((pairEulerPolynomial A B).eval (q ^ (-s)))⁻¹`. When `A`, `B` are the spectra of two
  presentations at `v` and `q = q_v`, this value is the Library's
  `partialEulerFactor P P' hP hP' v s` by definition.

### The modulus character against the spherical Whittaker values

- `sum_sub_of_lt_eq λ`: `∑_(i<j) (λ_i - λ_j) = ∑_i (n - 2i) λ_i`, so
  `δ_B⁻¹(ϖ^λ) = q ^ (∑_i (n - 2i) λ_i)`.
- `halfModulus_mul_self q λ`: `halfModulus q λ * halfModulus q λ = q ^ (-∑_i (n - 2i) λ_i)`
  (an integer power of `(q : ℂ)`).
- `zpow_mul_halfModulus_mul_self`: for `q > 0`,
  `q ^ (∑_i (n - 2i) λ_i) * (halfModulus q λ * halfModulus q λ) = 1`.
- `torusTerm_eq_equalRankLocalTerm`: for `q > 0`,
  `q ^ (∑_i (n - 2i) λ_i) * ((if λ antitone then halfModulus q λ * s_λ(a) else 0) *
  (if λ antitone then halfModulus q λ * s_λ(b) else 0) * (if λ_n ≥ 0 then t ^ |λ| else 0))`
  equals `equalRankLocalTerm a b t λ`. The two `if`-factors are the torus values of the
  spherical Whittaker functions given by the Library's `sphericalWhittaker_torus`.
- `exp_mul_log_zpow_eq_spectralPoint_pow`: for `q > 0` and `k : ℕ`,
  `exp (s · log (q ^ (-k))) = (q ^ (-s)) ^ k`. This is the form in which the Library's
  `detPower` (`exp (s · log ‖det g‖)`) records the factor `|det ϖ^λ|_v ^ s` when
  `|det ϖ^λ|_v = q^(-|λ|)`.

## Provenance

Internal supporting results for the proof of `EqualEulerFactorizationStatement`
(Cogdell 2004, §2.3, with Theorem 3.3, printed p.215). At an unramified place the
equal-rank local integral is computed by the Iwasawa decomposition. On the cell
`N ϖ^λ K` the integrand contributes
`δ_B⁻¹(ϖ^λ) W°_a(ϖ^λ) W°_b(ϖ^λ) Φ°(e_n ϖ^λ) |det ϖ^λ|^s`. The Shintani formula gives
`W°_a(ϖ^λ) = δ_B^(1/2)(ϖ^λ) s_λ(a)` for dominant `λ` and `0` otherwise, and
`Φ°(e_n ϖ^λ) = 1` exactly when `λ_n ≥ 0`. The Cauchy identity
`∑_λ s_λ(a) s_λ(b) t^|λ| = ∏_(i,j) (1 - a_i b_j t)⁻¹` then gives the local factor
`L(s, Π_v × Π'_v)`. This is the computation of Jacquet–Piatetski-Shapiro–Shalika
(*Rankin–Selberg convolutions*, 1983), recalled in Cogdell 2004 §2.3. This module proves the
summation and the torus-term identity. The radius `localRadius` is derived here; it is chosen
so that one half-plane `Re s > σ` serves every place at once, given a uniform Satake bound
`‖α‖ ≤ q_v ^ C`.

## Proof

- **Local sum.** `satakeSchur_eq_eval_jacobiTrudi` identifies `s_λ(a)` on dominant
  weights with `λ_n ≥ 0` with the Library's Jacobi–Trudi value of the natural weight
  `λ`. So `equalRankLocalTerm` restricted to the image of `natWeight` is the Library's
  `schurPairTerm`, and it vanishes off that image (`equalRankLocalTerm_eq_zero`).
  `Function.Injective.hasSum_iff` reduces the sum over `ℤ`-weights to the sum over
  antitone natural weights. There, `summable_norm_schurPairTerm_of_bounds` (with the rate
  `completeGrowthRate ^ (n + 1)` from `norm_jacobiTrudiValue_le` and
  `norm_jacobiTrudiValue_le_rate`) gives absolute summability when
  `pairGrowth a b * ‖t‖ < 1`. `tsum_schurPairTerm_eq_seriesValue` and
  `seriesValue_complexCauchySeries` evaluate the sum as the Cauchy product. The latter
  needs `‖a_i b_j t‖ < 1`, which follows from `‖a_i‖ ≤ completeGrowthRate ^ (n + 1)`.
- **Radius.** `1 + ∑ ‖x_i‖ ≤ 1 + (n + 1) q^(C⁺) ≤ (n + 2) q^(C⁺) ≤ 2^(n+1) q^(C⁺) ≤
  q^(n+1) q^(C⁺)`, using `q^(C⁺) ≥ 1` and `q ≥ 2`. Raising to the power `n + 1` and
  multiplying the two bounds gives `pairGrowth a b ≤ q ^ localRadius`. Then
  `‖q^(-s)‖ = q^(-Re s)` (`Complex.norm_natCast_cpow_of_pos`), and
  `q ^ (localRadius - Re s) < 1` because `q > 1` and the exponent is negative.
- **Euler factor.** `pairEulerPolynomial_ofTuple` writes the pair Euler polynomial as
  `∏_i ∏_j (1 - C(a_i b_j) X)`; evaluating gives `eval_pairEulerPolynomial_ofTuple`.
  The bounds on `A`, `B` give the bounds on each `a_i`, `b_j` through `mem_ofTuple`, and
  `hasSum_equalRankLocalTerm` applies.
- **Torus term.** `sum_sub_of_lt_eq` splits the double sum and counts
  `#{j | i < j} = n - i` (`Fin.card_Ioi`) and `#{i | i < j} = j` (`Fin.card_Iio`).
  `halfModulus_mul_self` combines the two real square roots into `q` (`Real.mul_self_sqrt`).
  The torus-term identity is a case split on dominance and on `λ_n ≥ 0`.
- **Determinant factor.** `Real.log_zpow`, `Complex.cpow_def_of_ne_zero` and
  `Complex.exp_nat_mul` give `exp (s · (-k) log q) = (exp (log q · (-s))) ^ k`.
