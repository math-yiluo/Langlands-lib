# Cutoff estimates for constant-coefficient elliptic operators on nested balls

Module `Langlands.Analysis.LocalEllipticCutoffEstimate`, namespace
`Langlands.Analysis`. It imports the published statement module
`Langlands.Analysis.ConstantCoefficientEllipticL2EstimateStatement`, the ball
cutoff module `Langlands.Analysis.EuclideanBallCutoff` and the iterated
derivative module `Langlands.Analysis.SmoothIteratedFDerivSymm`.

## Conventions

`d` and `r` are natural numbers, and `V = EuclideanSpace ℝ (Fin d)` carries its
Euclidean norm, its `volume` measure and its standard orthonormal basis
`e = EuclideanSpace.basisFun (Fin d) ℝ`. A word of length `j` is a function
`w : Fin j → Fin d`. `e ∘ w` is the family `i ↦ e (w i)`. Every ordered word is
counted once, including words with repeated letters.

"Smooth" means `ContDiff ℝ ∞` or `ContDiffOn ℝ ∞`, with `open scoped ContDiff`.
Here `∞` is the `C^∞` level of `ℕ∞ω`, not the analytic level `ω`. `D^j F(x)` is
Mathlib's `iteratedFDeriv ℝ j F x`, and `‖D^j F(x)‖` is its operator norm.
`ball x₀ ρ` is the open ball `Metric.ball x₀ ρ`. `‖G‖_{L²(B)}` abbreviates
`eLpNorm G 2 (volume.restrict B)`. All `L²` norms and weighted seminorms are
extended nonnegative reals (`ℝ≥0∞`) and may be `∞`. Real constants enter
through `ENNReal.ofReal`, which sends negative reals to `0`. `exp` is
`Real.exp`, `C(k, i)` is `Nat.choose k i`, and `-` on naturals is truncated
subtraction.

`ζ = ballCutoff x₀ ρ R` is the cutoff of the ball cutoff module. For
`0 ≤ ρ < R` it is smooth, takes values in `[0, 1]`, equals `1` near every point
of `ball x₀ ρ`, has closed support in `closedBall x₀ ((ρ + R) / 2)`, and
satisfies `‖D^k ζ(x)‖ ≤ ballCutoffConst k / (R - ρ)^k` for all `k` and `x`.
`iteratedLineDeriv ℝ p u v x = D^p u(x)(v)` is the line derivative of the
iterated derivative module.

In the results below, `a : (Fin r → Fin d) → ℂ` is an arbitrary coefficient
array, `A = ∑_w ‖a w‖`, and `P = constCoeffAction a`.

## Definitions

- `derivWordNorm j F x = √(∑_{w : Fin j → Fin d} ‖D^j F(x)(e ∘ w)‖²)` for
  `F : V → ℂ`. It is the Euclidean norm of the ordered tensor of `j`-th
  derivatives of `F` at `x`. It is a real number `≥ 0`.
- `constCoeffAction a F x = ∑_{w : Fin r → Fin d} a w · D^r F(x)(e ∘ w)`, the
  constant-coefficient operator of order `r` with coefficient array `a`, applied
  to `F : V → ℂ`. The values are complex.
- `ballWeightedSeminorm G x₀ R m` is the extended real number

    `⨆_{ρ ∈ [R/2, R)} ENNReal.ofReal ((R - ρ)^m) · ‖G‖_{L²(ball x₀ ρ)}`

  for `G : V → ℝ`, a centre `x₀`, a real `R` and an exponent `m : ℕ`. The
  interval is `Set.Ico (R / 2) R`. If `R ≤ 0`, it is empty and the supremum is
  `0`.
- `ConstCoeffL2Bound a K S` is the proposition that every smooth `F : V → ℂ`
  with compact support and `tsupport F ⊆ S` satisfies

    `eLpNorm (derivWordNorm r F) 2 volume ≤
      ENNReal.ofReal K · eLpNorm (constCoeffAction a F) 2 volume`.

  Here `K` is real and `S` is a set in `V`. This is the a priori estimate for
  `P` on test functions supported in `S`.

## Results

### Finite sums and `L²`

- `ennreal_l2_sum_le` (Minkowski in `ℓ²`): for finsets `t`, `s` and
  `f : κ → ι → ℝ≥0∞`,
  `(∑_{i ∈ t} (∑_{q ∈ s} f q i)^2)^{1/2} ≤ ∑_{q ∈ s} (∑_{i ∈ t} (f q i)^2)^{1/2}`.
- `ennreal_l2_const_mul`: `(∑_{i ∈ t} (c · f i)^2)^{1/2} = c · (∑_{i ∈ t} (f i)^2)^{1/2}`.
- `ennreal_l2_mono`: the `ℓ²` expression is monotone in the family on `t`.
- `eLpNorm_sqrt_sum_sq`: for finitely many real functions `g i`, each
  a.e.-strongly measurable for `μ`,
  `eLpNorm (x ↦ √(∑_i g i x^2)) 2 μ = (∑_i (eLpNorm (g i) 2 μ)^2)^{1/2}`.
- `pow_le_exp_mul_pow_shrink`: for real `t ≥ 0` and naturals with `m ≤ r + p`,
  `t^m ≤ exp(r + 1) · (t (p + 1) / (p + 2))^m`.
- `pow_mul_factorial_sub_le`: in `ℕ`, `(p + 2)^q · (p - q)! ≤ (q + 2)^q · p!`,
  with truncated subtraction.

### Basic facts

- `ConstCoeffL2Bound.mono`: the bound on `T` gives the bound on every `S ⊆ T`.
- `ConstCoeffL2Bound.of_le`: the bound with `K` gives the bound with every
  `K' ≥ K`.
- `constCoeffL2Bound_of_statement`: assume the proposition
  `ConstantCoefficientEllipticL2EstimateStatement d r` as a hypothesis. Let
  `c > 0`, and assume the symbol lower bound
  `c ‖ξ‖^r ≤ ‖∑_w a w · ∏_{j : Fin r} ξ (w j)‖` for every `ξ : V`. Then
  `ConstCoeffL2Bound a c⁻¹ S` holds for every set `S`. This module does not
  prove that proposition. It only shows that the published statement has the
  form of `ConstCoeffL2Bound`.
- `derivWordNorm_nonneg`, `derivWordNorm_sq` (the square is the sum of
  squares) and `norm_basisFun` (`‖e i‖ = 1`).
- `norm_iteratedFDeriv_le_derivWordNorm`: `‖D^j F(x)‖ ≤ derivWordNorm j F x`.
  The operator norm is at most the ordered word norm.
- `derivWordNorm_congr_of_eventuallyEq`: functions that agree near `x` have the
  same word norms at `x`.
- `continuousOn_iteratedFDeriv_of_isOpen`, `continuousOn_derivWordNorm` and
  `continuousOn_constCoeffAction`: for `U` smooth on an open set `s`, the maps
  `D^j U`, `derivWordNorm j U` and `constCoeffAction a U` are continuous on
  `s`. The first holds for any real normed codomain.
- `le_ballWeightedSeminorm`: for `ρ ∈ [R/2, R)`, each term
  `ENNReal.ofReal ((R - ρ)^m) · ‖G‖_{L²(ball x₀ ρ)}` is at most
  `ballWeightedSeminorm G x₀ R m`.

### The Leibniz commutator of the cutoff

`norm_iteratedFDeriv_ballCutoff_smul_sub_le` holds on any real inner product
space `E`, for `U : E → F` with `F` a real normed space. Assume `0 ≤ ρ < R`,
`U` smooth on `ball x₀ R`, `x ∈ ball x₀ R` and `k : ℕ`. Then

`‖D^k (ζ • U)(x) - ζ(x) • D^k U(x)‖ ≤
  ∑_{i=1}^{k} C(k, i) · (ballCutoffConst i / (R - ρ)^i) · ‖D^(k-i) U(x)‖`.

The term with `i = 0` of the Leibniz formula is removed. Only derivatives of
order `≥ 1` of the cutoff remain.

### The localised estimate (Morrey–Nirenberg Lemma 5.2)

Assume `0 ≤ ρ < R` and `U : V → ℂ` smooth on `ball x₀ R`.

- `norm_constCoeffAction_ballCutoff_smul_le`: for `x ∈ ball x₀ R`,

    `‖P(ζ • U)(x)‖ ≤ ‖P U(x)‖ +
      ∑_{q=1}^{r} A · C(r, q) · (ballCutoffConst q / (R - ρ)^q) · derivWordNorm (r - q) U x`.

- `eLpNorm_derivWordNorm_ball_le` (scalar form): if in addition
  `ConstCoeffL2Bound a K (ball x₀ R)` holds, then

    `‖derivWordNorm r U‖_{L²(ball x₀ ρ)} ≤
      ENNReal.ofReal K · ‖P U‖_{L²(ball x₀ R)} +
      ∑_{q=1}^{r} ENNReal.ofReal (K · (A · C(r, q) · (ballCutoffConst q / (R - ρ)^q)))
        · ‖derivWordNorm (r - q) U‖_{L²(ball x₀ R)}`.

- `eLpNorm_sqrt_sum_derivWordNorm_ball_le` (family form): the same estimate
  for a family `U i`, `i` in a finite type, of functions smooth on
  `ball x₀ R`. Each `L²` norm is taken of the pointwise Euclidean norm of the
  family: `√(∑_i derivWordNorm r (U i) x^2)` on the left,
  `√(∑_i ‖P (U i) x‖^2)` and `√(∑_i derivWordNorm (r - q) (U i) x^2)` on the
  right. The constants are those of the scalar form.

### Regrouping derivative words

Let `u : V → ℂ` be smooth on an open set `s` and `x ∈ s`. Write
`∂_{w'} u = iteratedLineDeriv ℝ p u (e ∘ w')` for a word `w'` of length `p`.

- `append_basisFun`: `Fin.append (e ∘ w) (e ∘ w') = e ∘ Fin.append w w'`.
- `sum_sq_derivWordNorm_iteratedLineDeriv` and its square-root form
  `sqrt_sum_sq_derivWordNorm_iteratedLineDeriv`:

    `∑_{w' : Fin p → Fin d} derivWordNorm j (∂_{w'} u) x^2 = derivWordNorm (j + p) u x^2`.

- `constCoeffAction_iteratedLineDeriv`: `P(∂_{w'} u)(x) = D^p (P u)(x)(e ∘ w')`.
  The operator commutes with line derivatives.
- `sqrt_sum_sq_norm_constCoeffAction_iteratedLineDeriv`:
  `√(∑_{w'} ‖P(∂_{w'} u)(x)‖^2) = derivWordNorm p (P u) x`.

### The weighted recursion (Morrey–Nirenberg Lemma 5.3)

Let `u : V → ℂ` be smooth on `ball x₀ R`. Write

- `N m = ballWeightedSeminorm (derivWordNorm m u) x₀ R m`, and
- `M p = ballWeightedSeminorm (derivWordNorm p (P u)) x₀ R (r + p)`.

In `N m` the derivative order and the weight exponent are both `m`. In `M p`
the derivative order is `p` and the weight exponent is `r + p`.

- `ballWeightedSeminorm_add_le`: if `K ≥ 0` and
  `ConstCoeffL2Bound a K (ball x₀ R)`, then for every `p : ℕ`

    `N (r + p) ≤ ENNReal.ofReal (exp(r + 1) · K) · M p +
      ∑_{q=1}^{r} ENNReal.ofReal (exp(r + 1) · K · (A · C(r, q) · ballCutoffConst q) · (p + 2)^q)
        · N (r + p - q)`.

- `exists_factorial_weighted_recursion`: for fixed `a` and real `K` there is a
  real `K₃ > 0` such that, for every centre `x₀`, radius `R`, function `u`
  smooth on `ball x₀ R` with `ConstCoeffL2Bound a K (ball x₀ R)`, and every
  `p : ℕ`,

    `(1/p!) · N (r + p) ≤ K₃ · ((1/p!) · M p +
      ∑_{q=1}^{r} (1/(p - q)!) · N (r + p - q))`.

  Here `p - q` is truncated subtraction, so `(p - q)! = 1` when `q ≥ p`. The
  factors `1/p!`, `1/(p - q)!` and `K₃` enter through `ENNReal.ofReal`. The
  constant `K₃` depends only on `d`, `r`, `a` and `K`, not on `x₀`, `R`, `u`
  or `p`. The proof takes

    `K₃ = exp(r + 1) · max K 0 · (1 + S) · (r + 2)^r + 1`, where
    `S = ∑_{q=1}^{r} A · C(r, q) · ballCutoffConst q`.

  The statement only asserts that some such `K₃` exists.

## Proof outline

**Scalar Lemma 5.2.** Put `F = ζ • U`. By the ball cutoff module, `F` is
smooth on `V`, has compact support, and its closed support lies in
`closedBall x₀ ((ρ + R)/2) ⊆ ball x₀ R`. Near every point of `ball x₀ ρ`, `F`
agrees with `U`. So the two have the same word norms on `ball x₀ ρ`. Hence
`‖derivWordNorm r U‖_{L²(ball x₀ ρ)}` is at most the `L²` norm of
`derivWordNorm r F` on `V`. `ConstCoeffL2Bound` bounds that by `K` times
`‖P F‖_{L²}`. Since `D^r F` vanishes outside `tsupport F`, this norm equals
`‖P F‖_{L²(ball x₀ R)}`. On `ball x₀ R`, write
`P F = ζ · P U + ∑_w a w · T(e ∘ w)`, where
`T = D^r F(x) - ζ(x) • D^r U(x)`. Then `|ζ| ≤ 1`, and `‖T(e ∘ w)‖ ≤ ‖T‖`
because `‖e i‖ = 1`. The Leibniz commutator bound controls `‖T‖`, and
`‖D^(r-q) U‖ ≤ derivWordNorm (r - q) U` finishes the pointwise bound. The
triangle inequality in `L²` and `eLpNorm_const_smul` give the integrated form.
Measurability comes from continuity on the open ball.

**Family form.** Apply the scalar form to each `U i`. Then combine
`eLpNorm_sqrt_sum_sq` with Minkowski's inequality in `ℓ²` over `i`
(`ENNReal.Lp_add_le`, `ennreal_l2_sum_le`) and `ennreal_l2_const_mul`.

**Regrouping.** By `iteratedLineDeriv_iteratedLineDeriv` from the iterated
derivative module,
`D^j(∂_{w'} u)(x)(e ∘ w) = D^{j+p} u(x)(e ∘ Fin.append w w')`. The pairs
`(w, w')` correspond bijectively to words of length `j + p` through
`Fin.appendEquiv`. Commuting `P` with `∂_{w'}` uses the same nesting formula and
the symmetry `iteratedFDeriv_append_comm_of_contDiffAt`, which exchanges the
blocks `w` and `w'`.

**Weighted recursion.** Fix `ρ ∈ [R/2, R)`, put `t = R - ρ` and
`ρ' = ρ + t/(p + 2)`. Then `ρ < ρ' < R`, `ρ' ∈ [R/2, R)` and
`R - ρ' = t (p + 1)/(p + 2)`. Apply the family form of Lemma 5.2 on the pair of
balls `ball x₀ ρ ⊂ ball x₀ ρ'` to the family `(∂_{w'} u)_{w'}` over all words
`w'` of length `p`. The bound restricts from `ball x₀ R` to `ball x₀ ρ'` by
`ConstCoeffL2Bound.mono`. Regrouping turns the three family norms into
`derivWordNorm (r + p) u` on `ball x₀ ρ`, `derivWordNorm p (P u)` on
`ball x₀ ρ'` and `derivWordNorm (r + p - q) u` on `ball x₀ ρ'`. Multiply by
`t^{r+p}`. Since `ρ' - ρ = t/(p + 2)`, each lower term has
`t^{r+p} / (t/(p+2))^q = (p + 2)^q t^{r+p-q}`. Then
`pow_le_exp_mul_pow_shrink` gives `t^m ≤ exp(r + 1) (R - ρ')^m` for
`m ≤ r + p`. Each term is now a weighted `L²` norm on `ball x₀ ρ'` with
`ρ' ∈ [R/2, R)`, so `le_ballWeightedSeminorm` bounds it. Taking the supremum
over `ρ` gives `ballWeightedSeminorm_add_le`.

**Factorial normalisation.** Replace `K` by `max K 0` (`ConstCoeffL2Bound.of_le`)
and multiply by `1/p!`. For `1 ≤ q ≤ r`, `pow_mul_factorial_sub_le` and
`q ≤ r` give `(p + 2)^q / p! ≤ (r + 2)^r / (p - q)!`. Each coefficient
`A · C(r, q) · ballCutoffConst q` is at most `S`. This gives the stated `K₃`.

## Provenance

The source is Morrey–Nirenberg 1957, "On the analyticity of the solutions of
linear elliptic systems of partial differential equations" (registered source
`provided-17e51270c6d50eab8ff7b4142058b4ec69474b21e75225ec9952a95784e8229f`),
§5 (printed pages 287–289, PDF pages 17–19), with the notation of §3 (printed
pages 278–281, PDF pages 8–11). On p. 287 they say that they "formulate lemmas
analogous to those of §§2–4 and omit the proofs which are very similar".
Lemma 5.1 nonetheless gets a short Fourier-transform proof (pp. 288–289). Lemma 5.2
is derived "By the argument used to deduce Lemma 3.2", and Lemma 5.3 "as in
the proof of Lemma 3.4" (p. 289). The following was checked against rendered
images of those pages.

- Their (5.6) is the system `L^0_{jk} u^k = f_j` with constant coefficients and
  only derivatives of order `s_j + t_k`.
- (5.3) defines
  `e_p(f, B_r) = [∫_{B_r} Σ_{j=1}^N |∇^{s-s_j+p} f_j|² dx]^{1/2}` for `p ≥ 0` and
  `d_p(u, B_r) = [∫_{B_r} Σ_{j=1}^N |∇^{s+t_j+p} u^j|² dx]^{1/2}` for
  `p ≥ -(s+t)`, with `∇^q φ = 0` if `q < 0`.
- The norm `|∇^q φ|` in (5.3) is the one of §2 (printed p. 275, PDF p. 5).
  With the sub- and superscripts of `V` dropped, (2.1) reads "|V|² = sum of
  squares of absolute values of all components of V". By (2.2), `∇^q φ` is the
  tensor of `q`-th derivatives `φ_{,γ₁…γ_q}`, where "the indices γ₁, ···, γ_p
  are supposed to be independent of the other indices". So
  `|∇^q φ|` is the square root of the sum of `|∂_{γ₁}⋯∂_{γ_q} φ|²` over all
  ordered index words `(γ₁, …, γ_q)`. This is exactly `derivWordNorm q φ`, so
  the norm agrees with the source.
- (3.12) sets `[p!] = p!` if `p ≥ 0` and `[p!] = 1` if `p < 0`.
- (5.4) defines
  `M_{R,p}(f) = (p!)^{-1} sup_{R/2 ≤ r < R} (R - r)^{s+t+p} e_p(f, B_r)` for
  `p ≥ 0` and
  `N_{R,p}(u) = [p!]^{-1} sup_{R/2 ≤ r < R} (R - r)^{s+t+p} d_p(u, B_r)` for
  `p ≥ -s-t`.
- Lemma 5.1 (p. 288): "Suppose u satisfies (5.6) in B_R and vanishes in a
  neighborhood of the boundary of B_R. Then (5.7) d_0(u, B_R) ≤ K_1 e_0(f, B_R)."
- Lemma 5.2 (printed p. 289): "Suppose u satisfies (5.6) in B_R. There is a
  constant K_2 such that, for 0 < r < r+δ < R, r > δ,
  d_0²(u, B_r) ≤ K_2{e_0²(f, B_{r+δ}) + Σ_{q=1}^{s+t} d²_{-q}(u, B_{r+δ}) δ^{-2q}}."
- They then apply this "with δ = (R-r)/(p+1) to each component of ∇^p u" and
  obtain Lemma 5.3, (5.9): "If u satisfies (5.6) in B_R then
  N_{R,p}(u) ≤ K_3{M_{R,p}(f) + Σ_{q=1}^{s+t} N_{R,p-q}(u)}, p > 0."

This module is a derived variant, proved independently. The dictionary is
`f = P u` and `s + t = r`. Their `N_{R,p}(u)` corresponds to
`(1/p!) · N (r + p)`, and their `M_{R,p}(f)` corresponds to `(1/p!) · M p`.
Their `N_{R,p-q}(u)` corresponds to `(1/(p - q)!) · N (r + p - q)`. The
differences are:

- Only the scalar case is treated: one complex equation for one unknown
  (`N = 1`), of order `r`, with constant coefficients `a`.
- Balls are open balls `ball x₀ ρ` with an arbitrary centre `x₀`. The pair
  `B_r ⊂ B_{r+δ}` of Lemma 5.2 becomes `ball x₀ ρ ⊂ ball x₀ R`, with `R - ρ` in
  place of `δ`. The only condition is `0 ≤ ρ < R`. There is no condition
  `r > δ`, because the quadratic cutoff of the ball cutoff module is smooth at
  the centre.
- `u` is an arbitrary function smooth on the open ball. No equation is assumed:
  the right-hand sides use `P u` directly.
- Lemma 5.1 is not proved here. It enters as the hypothesis
  `ConstCoeffL2Bound a K (ball x₀ R)`. `constCoeffL2Bound_of_statement` derives
  that hypothesis from the published proposition
  `ConstantCoefficientEllipticL2EstimateStatement d r`, taken as a hypothesis.
  The Library proves that proposition separately, as
  `constantCoefficientEllipticL2Estimate` in
  `Langlands.Analysis.ConstantCoefficientEllipticL2EstimateProof`. This module
  does not import that proof.
- Lemma 5.2 is stated without squares, with explicit constants
  `K · A · C(r, q) · ballCutoffConst q`. The family form replaces the
  application "to each component of ∇^p u".
- Lemma 5.3 uses `δ = (R - ρ)/(p + 2)` instead of `(R - r)/(p + 1)`, so that
  the larger radius `ρ'` stays in `[R/2, R)`. It holds for every `p ≥ 0`,
  including `p = 0`. Since `p - q` is truncated subtraction, `(p - q)!` equals
  their `[(p - q)!]` of (3.12) for every `q`: both are `1` when `q ≥ p`.
- All norms are extended. The weighted seminorms may be `∞`, and then the
  inequalities hold in `ℝ≥0∞`.
