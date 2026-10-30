# Pointwise derivative bounds from local L² bounds

Module `Langlands.Analysis.LocalSobolevPointwise`, namespace
`Langlands.Analysis`.

## Conventions

`E` is a real normed space (`NormedAddCommGroup` with `NormedSpace ℝ`).
From the averaged estimates on, `E` is finite-dimensional, carries its
Borel σ-algebra, and `μ` is an additive Haar measure on `E`
(`μ.IsAddHaarMeasure`). `d = finrank ℝ E`, and every dimension, including
`d = 0`, is allowed. `G` is a real normed space. The Taylor-based results
also assume `G` complete (`CompleteSpace G`), because they use
Bochner integrals with values in `G`.

`D^k u(y)` means Mathlib's `iteratedFDeriv ℝ k u y`, a continuous
`k`-multilinear map `E^k → G`, and `‖D^k u(y)‖` is its operator norm.
"Smooth on `U`" means `ContDiffOn ℝ ∞ u U`, with `∞` the smooth (`C^∞`)
level of `ℕ∞ω`, not the analytic level `ω`. `B = ball x ρ` is the open
ball. `‖f‖_{L²(B)}` is `eLpNorm f 2 (μ.restrict B)`, the extended
nonnegative number `(∫_B ‖f‖² dμ)^{1/2}`. For a derivative this uses the
operator norm. The averaged estimates are inequalities in `ℝ≥0∞`. There
`‖v‖ₑ` is the extended norm of `v`, and real coefficients enter through
`ENNReal.ofReal`.

## The definition

`euclideanBasisWordNorm T`: for `d k : ℕ` and a continuous `k`-multilinear
map `T` from `(EuclideanSpace ℝ (Fin d))^k` to `G`, this is the real number

  `√( ∑_{w : Fin k → Fin d} ‖T (e_{w 0}, …, e_{w (k-1)})‖² )`,

where `e = EuclideanSpace.basisFun (Fin d) ℝ` is the standard orthonormal
basis. The sum runs over all ordered words `w`, so a mixed derivative is
counted once for each order of its arguments. The theorem
`euclideanBasisWordNorm_def` records this formula (it holds by `rfl`).
For `k = 0` there is exactly one (empty) word, and the value is the norm of
`T` at the empty tuple. When `G = ℝ` it is the Hilbert–Schmidt norm of `T` in
the standard basis. For `T = D^k F(y)` it is the square root of the sum of
the squared norms of all `k`-th order partial derivatives of `F` at `y`, one
term for each order of differentiation.

## Results

### Derivative bookkeeping

- `norm_iteratedFDeriv_iteratedFDeriv`: for every `f : E → G`, every `x`
  and all `k, j`, `‖D^k (D^j f)(x)‖ = ‖D^(k+j) f(x)‖`. No smoothness is
  needed: both sides use Mathlib's iterated derivatives, junk values
  included.
- `continuousOn_iteratedFDeriv_ball` and `contDiffOn_iteratedFDeriv_ball`:
  if `u` is smooth on `ball x ρ`, then every `D^k u` is continuous on that
  ball, and also smooth on it.

### Taylor's formula in norm

`enorm_le_sum_add_lintegral_of_mem_ball` (with `G` complete): let `u` be
smooth on `ball x ρ`, let `y ∈ ball x ρ`, and let `n : ℕ`. Then

  `‖u x‖ₑ ≤ ∑_{k=0}^{n} (ρ^k / k!) ‖D^k u(y)‖ₑ
           + (ρ^(n+1) / n!) ∫_{(0,1)} (1 - t)^n ‖D^(n+1) u(y + t (x - y))‖ₑ dt`.

### Haar measure lemmas

- `ofReal_pow_finrank_mul_setLIntegral_ball_homothety_le`: for any
  `h : E → ℝ≥0∞`, any centre `x`, any radius `ρ` and `0 < c ≤ 1`,

    `c^d ∫_{ball x ρ} h (x + c (y - x)) dμ(y) ≤ ∫_{ball x ρ} h dμ`.

- `setLIntegral_enorm_le_measure_rpow_mul_eLpNorm`: for any measure `μ` on
  any measurable space, any set `s`, and any `f` that is a.e. strongly
  measurable for `μ.restrict s`, with values in any normed additive commutative group,

    `∫_s ‖f‖ₑ dμ ≤ μ(s)^{1/2} ‖f‖_{L²(μ.restrict s)}`.

  No Haar or finite-dimensionality hypothesis is used here.

### Averaged and local Sobolev estimates

In these three results `E` is finite-dimensional with Haar measure `μ`,
`G` is complete, `u` is smooth on `B = ball x ρ`, and `n` is a natural
number with `d ≤ n`. All bounds are at the centre `x` of the ball.

- `measure_ball_mul_enorm_le_sum_lintegral` (averaged Taylor estimate):

    `μ(B) ‖u x‖ₑ ≤ ∑_{k=0}^{n} (ρ^k / k!) ∫_B ‖D^k u‖ₑ dμ
                  + (ρ^(n+1) / n!) ∫_B ‖D^(n+1) u‖ₑ dμ`.

  No sign condition on `ρ` is needed: if `ρ ≤ 0` the ball is empty and
  the left side is `0`.

- `measure_ball_rpow_mul_enorm_le_sum_eLpNorm` (local Sobolev estimate):
  if moreover `0 < ρ`, then

    `μ(B)^{1/2} ‖u x‖ₑ ≤ ∑_{k=0}^{n} (ρ^k / k!) ‖D^k u‖_{L²(B)}
                       + (ρ^(n+1) / n!) ‖D^(n+1) u‖_{L²(B)}`.

- `measure_ball_rpow_mul_enorm_iteratedFDeriv_le` (the same for
  derivatives): if `0 < ρ`, then for every `j : ℕ`

    `μ(B)^{1/2} ‖D^j u(x)‖ₑ ≤ ∑_{k=0}^{n} (ρ^k / k!) ‖D^(k+j) u‖_{L²(B)}
                            + (ρ^(n+1) / n!) ‖D^(n+1+j) u‖_{L²(B)}`.

### Factorial transfer

- `factorial_add_le_two_pow_mul`: `(k + j)! ≤ 2^(k+j) k! j!` for all
  `k, j : ℕ`, as real numbers.

- `exists_norm_iteratedFDeriv_le_factorial_of_eLpNorm_le`: let `E` be
  finite-dimensional with Haar measure `μ` and `G` complete. Let `0 < R`,
  let `C, A` be arbitrary reals, and let `u` be smooth on `ball x₀ R`.
  Suppose that for every `k : ℕ`

    `‖D^k u‖_{L²(ball x₀ R)} ≤ ENNReal.ofReal (C · A^k · k!)`

  (with `μ`). Then there are reals `C', M'` such that

    `‖D^k u(y)‖ ≤ C' · M'^k · k!` for every `y ∈ ball x₀ (R / 2)` and every `k : ℕ`.

  One pair `C', M'` serves all points of the smaller ball and all orders.

### Euclidean interface

Here `E = EuclideanSpace ℝ (Fin d)` with its standard measure `volume`.

- `norm_le_euclideanBasisWordNorm`: for every continuous `k`-multilinear
  map `T` from `(EuclideanSpace ℝ (Fin d))^k` to any real normed space,
  `‖T‖ ≤ euclideanBasisWordNorm T`.

- `exists_norm_iteratedFDeriv_le_factorial_of_eLpNorm_euclideanBasisWordNorm_le`:
  let `G` be complete, `0 < R`, `C, A` arbitrary reals, and
  `F : EuclideanSpace ℝ (Fin d) → G` smooth on `ball x₀ R`. Suppose that for
  every `k : ℕ`

    `‖y ↦ euclideanBasisWordNorm (D^k F(y))‖_{L²(ball x₀ R)} ≤ ENNReal.ofReal (C · A^k · k!)`,

  where the `L²` norm is `eLpNorm _ 2 (volume.restrict (ball x₀ R))`. Then
  there are reals `C', M'` with `‖D^k F(y)‖ ≤ C' · M'^k · k!` for every
  `y ∈ ball x₀ (R / 2)` and every `k`.

  The definition unfolds by `rfl`. So the hypothesis may equally be given
  with the explicit function
  `y ↦ √(∑_{w : Fin k → Fin d} ‖D^k F(y)(e_{w 0}, …, e_{w (k-1)})‖²)`,
  which is the form used by the constant-coefficient `L²` statement in
  task `10d69993-68ea-4ade-a1cd-649023178c41`.

## Proofs

`norm_iteratedFDeriv_iteratedFDeriv` is proved by induction on `k`.
The step rewrites `D^(k+1) g` through `fderiv` (`norm_iteratedFDeriv_fderiv`),
uses `fderiv_iteratedFDeriv` to write `fderiv (D^j f)` as `D^(j+1) f`
composed with a linear isometry, and removes the isometry
(`LinearIsometryEquiv.norm_iteratedFDeriv_comp_left`). The two
continuity and smoothness lemmas come from Mathlib's lemmas on
`iteratedFDerivWithin` on the open ball (`iteratedFDerivWithin_of_isOpen`),
and from `ContDiffAt.iteratedFDeriv_right` at each point of the ball.

Taylor's formula in norm applies Mathlib's Taylor formula with integral
remainder, `map_add_eq_sum_add_integral_iteratedFDeriv`, to the segment
from `y` to `x`. The segment lies in the ball by convexity. Each term is
bounded with the operator norm and `‖x - y‖ ≤ ρ`
(`ContinuousMultilinearMap.le_opNorm_mul_pow_of_le`). The remainder is
bounded through `enorm_integral_le_lintegral_enorm`.

The homothety lemma uses three facts. The map `y ↦ x + c (y - x) = c y + a`
sends the ball into itself, because `c ≤ 1`. Pushing `μ` forward by
`y ↦ c y` gives `|c^(-d)| μ` (`Measure.map_addHaar_smul`). Haar measure is
translation invariant (`lintegral_add_right_eq_self`). The `L¹`–`L²` lemma
is the extended-valued form of Hölder's inequality
`eLpNorm_le_eLpNorm_mul_rpow_measure_univ` with exponents `1 ≤ 2`, applied
to `μ.restrict s`.

Averaged Taylor estimate: integrate the Taylor inequality in the base
point `y` over `B`. The first terms give the integrals of `‖D^k u‖ₑ`
directly. In the remainder, Tonelli's theorem
(`lintegral_lintegral_swap`) exchanges the `y`- and `t`-integrals; joint
measurability comes from continuity of `D^(n+1) u` on the ball. For fixed
`t ∈ (0, 1)`, write `y + t (x - y) = x + c (y - x)` with `c = 1 - t ∈ (0, 1]`.
Since `n ≥ d`, we have `c^n ≤ c^d`, so the homothety lemma bounds the inner
integral by `∫_B ‖D^(n+1) u‖ₑ dμ`. This is uniform in `t`, and `(0, 1)` has
length `1`. The hypothesis `n ≥ d` is used exactly here: the averaging
loses the factor `c^(-d)`, and the Taylor weight `(1 - t)^n` must absorb
it.

The local Sobolev estimate bounds each integral of the averaged estimate by
`μ(B)^{1/2}` times the `L²` norm (the `L¹`–`L²` lemma). It then cancels one
factor `μ(B)^{1/2}`, which is nonzero and finite for `0 < ρ`
(`measure_ball_pos`, `measure_ball_lt_top`). The version for derivatives
applies it to `D^j u`, which is smooth on the ball. Then
`norm_iteratedFDeriv_iteratedFDeriv` and `eLpNorm_congr_norm_ae` replace
`‖D^k (D^j u)‖` by `‖D^(k+j) u‖`.

`factorial_add_le_two_pow_mul` follows from
`(k + j)! = C(k + j, j) · k! · j!` and `C(k + j, j) ≤ 2^(k+j)`.

Factorial transfer. Put `ρ = R / 2`, `M' = 2|A|`, and

  `K = ∑_{k=0}^{d} ρ^k (2|A|)^k + (ρ^(d+1) / d!) (2|A|)^(d+1) (d+1)!`,

and let `w = μ(ball 0 ρ)^{1/2} > 0`. The proof takes `C' = |C| K / w`.
For `y ∈ ball x₀ (R / 2)` we have `ball y ρ ⊆ ball x₀ R`, so the hypotheses
give the `L²` bounds `|C| |A|^m m!` on `ball y ρ`. By translation
invariance `μ(ball y ρ) = μ(ball 0 ρ)` (`Measure.addHaar_ball_center`).
The derivative estimate with `n = d` at the centre `y` then gives
`w ‖D^j u(y)‖ ≤ ∑_{k ≤ d} (ρ^k / k!) |C| |A|^(k+j) (k+j)! + …`. Bounding
`(k + j)! ≤ 2^(k+j) k! j!` turns the right side into
`|C| K (2|A|)^j j!`.

`norm_le_euclideanBasisWordNorm` expands each argument in the standard
basis, `v_j = ∑_i v_j(i) e_i`. Multilinearity
(`ContinuousMultilinearMap.map_sum`, `map_smul_univ`) gives
`T v = ∑_w (∏_j v_j(w j)) • T (e ∘ w)`. The Cauchy–Schwarz inequality over
words (`Real.sum_mul_le_sqrt_mul_sqrt`) and the identity
`∑_w ∏_j |v_j(w j)|² = ∏_j ‖v_j‖²` (`Finset.prod_univ_sum` and
`EuclideanSpace.norm_sq_eq`) give `‖T v‖ ≤ euclideanBasisWordNorm T · ∏_j ‖v_j‖`.
The Euclidean interface follows from the general factorial transfer with
`μ = volume`, by monotonicity of the `L²` norm (`eLpNorm_mono_real`).

## Provenance and scope

The estimates are a derived variant of Morrey–Nirenberg 1957, Lemma 2.2,
and of the first step of the proof of Lemma 2.3 (printed page 276, PDF
page 6, registered source
`provided-17e51270c6d50eab8ff7b4142058b4ec69474b21e75225ec9952a95784e8229f`).
Lemma 2.2 there is the special case of Sobolev's lemma used by the paper.
With `d̃_j(u, G) = [∫_G |∇^j u|² dx]^{1/2}` (their (2.4)),
`G = G_R` or `B_R`, `ν` the dimension and `n = [ν/2]`, it states
`|u(x)| ≤ C₁ [∑_{j=0}^{n+1} R^{2j-ν} d̃_j²(u, G)]^{1/2}` at every point of
`G`, with `C₁` depending only on `ν`. The proof of Lemma 2.3 applies this to
each component of `∇^p u`, using `∇^j ∇^p u = ∇^(j+p) u`, and then uses
factorial bounds on the `d̃_j`.

The Lean results differ from the source as follows. They are proved
here; they are not translations of a printed proof.

- They bound `u` only at the centre of a full ball, not at every point of
  a half ball. Every point of the smaller ball `ball x₀ (R / 2)` is treated
  as the centre of its own ball of radius `R / 2`.
- They need derivatives up to order `n + 1` with `n ≥ dim E`, rather than
  `[ν/2] + 1`. This simpler averaged Taylor argument loses the sharp order
  but gives the same consequence for factorial bounds.
- The coefficients are explicit (`ρ^k / k!`, `ρ^(n+1) / n!`, and
  `μ(B)^{1/2}` on the left) instead of an unspecified `C₁`.
- They hold in any finite-dimensional real normed space with any additive
  Haar measure, use operator norms of iterated Fréchet derivatives, and
  allow values in any real Banach space.
- The factorial transfer uses one fixed radius gap `R / 2` and the
  inequality `(k + j)! ≤ 2^(k+j) k! j!`. It does not use the
  `(R - r)`-weighted bounds (2.6)–(2.7) of the source.

The Euclidean basis-word norm is an internal convention. It matches the
ordered-word convention of `Langlands.Analysis.CoordinateScalarDifferentialOperator`
and of statement task `10d69993-68ea-4ade-a1cd-649023178c41`. It is not
the paper's `|∇^j u|`, whose exact counting of mixed derivatives is not
used.

This module turns assumed `L²` factorial bounds into pointwise factorial
bounds. It proves no analyticity statement or elliptic estimate, and it
does not establish the assumed `L²` factorial bounds. The separate
factorial-derivative unit
(`Langlands.Analysis.FactorialDerivativeAnalyticity`, task
`879255af-5725-46b9-8cbd-0ef6ca611174`) is not imported here.

The original is C. B. Morrey Jr. and L. Nirenberg, *On the analyticity of
the solutions of linear elliptic systems of partial differential equations*,
Communications on Pure and Applied Mathematics **10** (1957), 271–290,
DOI `10.1002/cpa.3160100204`. The retained project file is
`literature/Morrey-Nirenberg - On the analyticity of the solutions of linear elliptic systems of partial differential equations (1957).pdf`,
SHA256 `61c74249e27625fd25cb0a33d3c77d90ab6b5306fc9bccddc7a6d5314229f915`.
