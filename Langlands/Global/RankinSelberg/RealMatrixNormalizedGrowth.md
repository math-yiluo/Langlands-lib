# Entire normalizations of strip growth for the real matrix zeta integrals

This module adds vertical-strip growth to the real square matrix functional equation of
`RealMatrixPairIdentity`. Multiplied by the inverse pair `L`-factors, the two real matrix zeta
integrals become entire functions of exponential growth on vertical strips. These satisfy the
normalized functional equation at every point. The conclusion uses `RealJacquet.HasRealPairNormalizedGrowth`, the predicate defined in
`RealLocalNormalizedGrowth` for the Library's real equal-rank and unequal-rank growth
interfaces.

Throughout, `n = r + 1`, `G = GL_n(ℝ)`, `ιg` is the inverse transpose, and
`realMatrixZeta μ f Φ s = ∫ Φ(g) f(g) |det g|^(s + r/2) dμ(g)`.

## Definitions

`HasRealMatrixNormalizedGrowth μ f Φ fd Φd D Dd` means that there are a real `σ` and functions
`N`, `Nd` on `ℂ` such that:

- `N` and `Nd` are entire (`Differentiable ℂ`);
- `N` and `Nd` have exponential growth on vertical strips (the Library's
  `HasStripExponentialGrowth`);
- for `σ < Re s`, `N(s) = D(s) · realMatrixZeta μ f Φ s` and
  `Nd(s) = Dd(s) · realMatrixZeta μ fd Φd s`.

It contains no functional equation; that is supplied separately at the end.

## Results

- `HasRealMatrixNormalizedGrowth.congr_factor`: the factors `D`, `Dd` may be replaced by
  pointwise equal functions.
- `HasRealMatrixNormalizedGrowth.scale`: suppose `fd((b·1)⁻¹ g) = ω · fd(g)` for all `g`, where
  `b·1` is the scalar matrix `realMatrixScalar b`. Then the property for
  `(f, Φ, fd, matrixTransform 1 Φ)` implies it for `(f, Φ, fd, matrixTransform b Φ)` with the
  same factors. The auxiliary result
  `HasRealMatrixNormalizedGrowth.scale.stripGrowth_realMatrixScaledDualFactor` shows that
  `realMatrixScaledDualFactor b ω s = ω · |b|^(n(1/2 − s))` has exponential growth on vertical
  strips.
- `HasRealMatrixNormalizedGrowth.shift`: if `F'(g) = |det g|^w F(g)` and
  `Fd'(g) = |det g|^(−w) Fd(g)`, the property for `(F, Fd)` with factors `D`, `Dd` implies it
  for `(F', Fd')` with factors `s ↦ D(s + w)` and `t ↦ Dd(t − w)`.
- `torusEpsilon_ne_zero`: the torus root number `torusEpsilon e` (a product of powers of `i`) is
  nonzero.
- `stripGrowth_torusL_inv`: `s ↦ (torusL e u s)⁻¹` has exponential growth on vertical strips.
- `realMatrixNormalizedGrowth_of_theta`: let `f`, `fd` be continuous with polynomial bounds
  `‖f g‖ ≤ C · height(g)^N` and `‖fd g‖ ≤ Cd · height(g)^Nd`, and let `Φ`, `Φd` be Schwartz. If
  the determinant theta identity for the pair `(detH e u, detK e u)` of
  `ArchimedeanDeterminantTheta` holds at every scale `a > 0`, then
  `HasRealMatrixNormalizedGrowth μ f Φ fd Φd (torusL e u)⁻¹ (torusL e (−u))⁻¹`.
- `realMatrixCompactNormalizedGrowthAtOne`: for `F(g) = ℓ(translate g f)`, where `ℓ` is a
  linear form with `HasCompactDerivativeBound` on the position principal series of `ds`, the
  property holds for `(F, Φ, F ∘ ιg, matrixTransform 1 Φ)` with the torus factors of the
  position signs and exponents of `ds`.
- `realMatrixCompactNormalizedGrowth`: the same at any Fourier parameter `b ∈ ℝˣ`.
- `realMatrixTwistedNormalizedGrowth`: the same for the determinant twist
  `F(g) = c(det g) · ℓ(translate g f)` by a real character datum `c`. The torus parameters are
  `eᵢ = signᵢ + parity(c)` and `uᵢ = exponentᵢ + exponent(c)`.

## Statement

`RealMatrixPairNormalizedGrowthStatement` has these hypotheses:

- `μ` is a Haar measure on `GL_n(ℝ)` and `κ` an s-finite Haar measure on `O(n)`;
- `es` is a list of real blocks with `realRank es = n`;
- `f` is a smooth section of the position principal series of `expand es`, and `ℓ` is a linear
  form on it with `HasCompactDerivativeBound`;
- `d` is a real character datum, `Φ` a Schwartz function on `n × n` real matrices, and
  `b ∈ ℝˣ`.

Put `F(g) = d(det g) · ℓ(translate g f)`. The statement asserts

`RealJacquet.HasRealPairNormalizedGrowth [character d] (expand es) ([character d].map dualBlock) ((expand es).map dualBlock) b √|b| _ 1 (realMatrixZeta μ F Φ) (realMatrixZeta μ (F ∘ ιg) (matrixTransform b Φ))`.

Spelled out, there are entire functions `N` and `Nd` of exponential growth on vertical strips
with the following properties.

- On some right half-plane, `N = L(s, [d] × expand es)⁻¹ · Z(s, F, Φ)` and
  `Nd = L(s, [d]^∨ × (expand es)^∨)⁻¹ · Z(s, F ∘ ιg, Φ̂_b)`, where `Φ̂_b = matrixTransform b Φ`.
  Here `L⁻¹` is the reciprocal-entire denominator of `realPairLFactor`, and `^∨` is the
  blockwise `dualBlock` map.
- `Nd(1 − s) = ε(s, [d] × expand es, b, √|b|) · N(s)` for every `s ∈ ℂ`, with `ε` the
  Library's `realPairEpsilon` and sign `1`.

`realMatrixPairNormalizedGrowth` proves it.

## Proof

1. **Theta step** (`realMatrixNormalizedGrowth_of_theta`). The zeta kernel factors as the base
   kernel `Φ(g) f(g) |det g|^(r/2)` times `|det g|^s` (`realMatrixZetaKernel_eq`). Apply
   `mellinPairPowerNormalizedGrowth` (module `ArchimedeanMellinPairPowerGrowth`) to the base
   kernels of `(f, Φ)` and `(fd, Φd)` with weight `|det g|`, the pair `(detH e u, detK e u)`,
   power `p = n`, `ε = torusEpsilon e`, `D = (torusL e u)⁻¹` and `Dd = (torusL e (−u))⁻¹`.
   - The two transform hypotheses are `mellin_detH` and `mellin_detK`.
   - `torusEpsilon_ne_zero` gives `ε ≠ 0`.
   - `stripGrowth_torusL_inv` gives the growth of `D` and `Dd`. Each factor
     `Γ_ℝ(s + uᵢ + eᵢ)⁻¹` is the denominator of the real Gamma block
     `GammaBlock.real (uᵢ + eᵢ)`, which has strip growth (`stripGrowth_denominator`), and
     `HasStripExponentialGrowth.finset_prod` handles the product.
   - The weighted integrability on `Re s ≥ T = n + 2 max(N, Nd) − r/2` is
     `integrable_realMatrixBaseKernel_power`.
   The functional equation produced by `mellinPairPowerNormalizedGrowth` is discarded here; only
   entireness, growth and agreement on the right half-plane are kept.
2. **Parameter one** (`realMatrixCompactNormalizedGrowthAtOne`). The coefficient `F` is continuous
   (`continuous_compactFunctionalCoefficient`) and polynomially bounded in the matrix height
   (`compactFunctionalGrowth`). The height is invariant under inverse transpose, so `F ∘ ιg` has
   the same bound. The theta identity at every scale is `realMatrix_functional_theta_at_one`.
   Step 1 then applies.
3. **Parameter `b`** (`realMatrixCompactNormalizedGrowth`). `realMatrixFunctionalCoefficient_dual_scalar`
   gives the scalar equivariance `(F ∘ ιg)((b·1)⁻¹ g) = (∏ᵢ χᵢ(b)) · (F ∘ ιg)(g)`.
   `HasRealMatrixNormalizedGrowth.scale` keeps `N` and replaces `Nd` by
   `realMatrixScaledDualFactor b ω · Nd`, using `realMatrixZeta_scaled_dual` at every `s`. The
   factor is entire (`differentiable_realMatrixScaledDualFactor`). Its norm is
   `‖ω‖ · |b|^(n(1/2 − Re s))`, which is bounded on each strip `a ≤ Re s ≤ a'` by
   `‖ω‖ (|b|^(n(1/2 − a)) + |b|^(n(1/2 − a')))`.
4. **Determinant twist** (`realMatrixTwistedNormalizedGrowth`). `exists_signTwist_coefficient`
   writes `c(det g) ℓ(translate g f) = |det g|^t ℓ'(translate g f')` for a
   compact-derivative-bounded `ℓ'` on the sign-twisted list, where `t` is the exponent of `c`.
   `detPower_inverseTranspose` turns the dual coefficient into `|det g|^(−t)` times the dual
   coefficient of `ℓ'`. Apply step 3 to `ℓ'`, then `HasRealMatrixNormalizedGrowth.shift` with
   `w = t`. The new normalizations are `N(s + t)` and `Nd(s − t)` on the half-plane
   `σ + |Re t| < Re s`. Translation preserves entireness and strip growth
   (`HasStripExponentialGrowth.div_add` with scale one), and `realMatrixZeta_shift` moves the
   zeta integrals. `torusL_signTwist_shift` and `torusL_neg_signTwist_shift` identify the
   translated factors with the twisted torus factors (`congr_factor`).
5. **Pair form** (`realMatrixPairNormalizedGrowth`).
   - `exists_expand_eq_map_character` writes `expand es = cs.map character` with
     `cs.length = n`.
   - `realMatrixPairIdentity_expand` (module `RealMatrixPairIdentity`) gives a half-plane
     `σ < Re s`, the meromorphic continuations `M`, `Md`, their agreement with the two matrix
     zeta integrals on that half-plane, and
     `RealJacquet.PairMeromorphicIdentity [character d] (expand es) b 1 M Md`. It also gives
     integrability and holomorphy of the integrals on the half-plane; the proof does not use
     these two clauses here.
   - The `RealJacquet.ContinuationPackage` is built from the remaining data: the half-plane
     bound `σ`, the continuations `M`, `Md`, their meromorphy, their agreement with the two
     integrals for `σ < Re s`, and the codiscrete equation of the pair identity. Its factors are
     the inverse denominators of `realPairLFactor` and its root number is `realPairEpsilon`.
   - Step 4 for the list `expand es` and the character `d` gives `N`, `Nd`. By `torusL_eq_pair`
     and `torusL_neg_eq_pair`, their torus factors `(torusL e u)⁻¹` and `(torusL e (−u))⁻¹` are
     the denominators of `realPairLFactor [character d] (expand es)` and of the dual pair.
   - `RealJacquet.hasRealPairNormalizedGrowth_of_continuationPackage` (module
     `RealLocalNormalizedGrowth`) combines the package with the entire normalizations and gives
     the normalized functional equation at every `s`.

## Scope

Only determinant twists of coefficients of the position principal series of `expand es` with a
supplied compact derivative bound are covered. The factors are those of the character list
`expand es`, not of `es`. For a discrete-series block of `es`, the principal series of
`expand es` has more Gamma poles than the discrete series, so the analogous statement for `es`
would need a separate argument. The theorem does not compare with Whittaker or
Langlands-quotient models and gives no bound uniform in `f` or `ℓ`.

Source: Hervé Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §4.7, Proposition 4.4,
pp. 30–31, as it is used in §8.1–§8.2, pp. 52–58 (literature id
`jacquet-2009-archimedean-rankin-selberg`). Jacquet takes the matrix equation from the
Godement–Jacquet theory; here it and the growth come from an explicit determinant theta pair.
Jacquet's additive parameter `a` corresponds to `b = −a`.
