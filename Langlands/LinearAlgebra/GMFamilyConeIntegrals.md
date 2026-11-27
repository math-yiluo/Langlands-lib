# Integrals of `c_M` of an exponential family against integrable tests

Module `Langlands.LinearAlgebra.GMFamilyConeIntegrals` computes
`∫ c_M(L(w)) u(w) dν(w)` for the `(G, M)`-family `c_S(λ) = e^{λ(y_S)}`, an
integrable test `u` on an s-finite measure space `(Ω, ν)` and a measurable
map `L : Ω → StrongDual ℝ a`, under the hypotheses of `integral_cM_exp_mul`:
a direction `μ` with `μ(v) ≠ 0` on the simple roots of every chamber, `L(w)`
nonzero on all these simple roots for almost every `w`, and for every chamber
`S` the Fourier integral of the phased test `w ↦ e^{iL(w)(y_S)} u(w)`
integrable on the orthant `{−μ(v) X_v > 0}`.

For `τ > 0` and `μ(v) ≠ 0`, each shifted reciprocal `θ_S(Λ + iτμ)⁻¹` is, up
to the Gram factor of the simple roots and an orientation sign, the
absolutely convergent damped Laplace integral over an oriented orthant in the
coordinates `Λ(v)`, `v ∈ Δ_S` (see "The spectral shift" below). As `τ → 0⁺`
two different limits occur. Pointwise, off the walls, `θ_S(Λ + iτμ)⁻¹`
converges to the ordinary reciprocal `θ_S(Λ)⁻¹`. After integration against
the test, the integrals converge to the undamped orthant integral of the
Fourier integral of the test; this is the boundary value in the sense of
distributions (Delorme). The two need not be compatible term by term: in rank
one, the integral of `(τ + ix)⁻¹ e^{−x²}` has real part tending to `π`, while
`(ix)⁻¹` is purely imaginary off `0` and not integrable against `e^{−x²}`.
Only the sum `c_M` over all chambers is integrated against `u` directly. The
integral of `c_M u` thus becomes a sum over chambers of Gram factors,
orientation signs and orthant integrals of Fourier integrals of the test. It
uses the oriented orthants `orientedOrthant`,
their signs `orthantSign` and the reciprocals
`orthantReciprocal d t y = ∏_i (t d_i + i y_i)⁻¹` of the Library module
`Langlands.Analysis.ConeFourierBoundary`.

## Results

- `orientedOrthant_eq`, `orthantReciprocal_eq`, `orthantSign_mul_self`,
  `measurableSet_orientedOrthant` from `ConeFourierBoundary` give the unfolding and measurability lemmas.
- `orthant_laplace` from `ConeFourierBoundary`: for `d_i ≠ 0` and `t > 0`, the function
  `x ↦ exp(−∑_i (t d_i + i y_i) x_i)` is integrable on the orthant
  `{d_i x_i > 0}` with integral `orthantSign d · orthantReciprocal d t y`
  (a product of one-dimensional complex exponential integrals over
  half-lines).
- `exp_orthant_exponent`: splits this exponential into the damping
  `e^{−t ∑ d_i x_i}` and the phase `e^{−i ∑ x_i y_i}`.
- `orthantReciprocal_integral'` (Fubini): for `d_i ≠ 0` for every `i`,
  `t > 0`, a measurable family of coordinates `y : Ω → (ι → ℝ)` on an
  s-finite measure space and an integrable `g`,
  `orthantSign d · ∫ orthantReciprocal d t (y w) g(w) dν` equals the
  damped orthant integral of the Fourier integral
  `x ↦ ∫ e^{−i ∑ x_i y_i(w)} g(w) dν`. This is the Library's
  `orthantReciprocal_integral` with the frequency space replaced by an
  arbitrary measure space and a measurable coordinate map.
- `tendsto_orthantReciprocal_integral`: let `d_i ≠ 0` for every `i`, let `y`
  be measurable and `g` integrable as above, and let the Fourier integral
  `x ↦ ∫ e^{−i ∑ x_i y_i(w)} g(w) dν` be integrable on the orthant. Then as
  `t → 0⁺` the unsigned reciprocal integrals
  `∫ orthantReciprocal d t (y w) g(w) dν` converge to `orthantSign d` times
  the undamped orthant integral of the Fourier integral. (For each `t > 0`,
  by the Fubini identity and `orthantSign d² = 1`, the unsigned integral is
  `orthantSign d` times the damped orthant integral; the damping exponent
  `t ∑ d_i x_i` is nonnegative on the orthant, so `tendsto_integral_remove_exponential_damping`
  of `Langlands.Analysis.ConeIntegralLimits` removes it.)
- `norm_orthantReciprocal_le`, `thetaShift_I_mul_inv`,
  `continuousAt_expShift_zero`, `expShift_zero`, `measurable_expShift`:
  `thetaShift a S Λ μ (iτ)⁻¹` is the Gram volume of the simple roots times
  `orthantReciprocal (−μ(v))_v τ (Λ(v))_v`; `expShift` at `0` is the
  Library's `cM` at `Λ`, is continuous at `0` when `Λ` is nonzero on all
  simple roots, and is measurable in `Λ`; for `d_i ≠ 0` and `t > 0`,
  `|orthantReciprocal d t y| ≤ ∏_i |t d_i|⁻¹`.
- `integral_cM_exp_mul`: let `y` give a `(G, M)`-family of exponentials, let
  `μ` be nonzero on all simple roots, let `L : Ω → StrongDual ℝ a` be
  measurable on an s-finite measure space `(Ω, ν)` with `L(w)` off the walls
  for almost every `w`, let `u` be integrable, and let the Fourier integrals
  of the tests `w ↦ e^{iL(w)(y_S)} u(w)` be integrable on the orthants
  `{−μ(v) X_v > 0}`. Then
  `∫ c_M(L(w)) u(w) dν = ∑_S gram(S) · orthantSign((−μ(v))_{v ∈ Δ_S}) ·
     ∫_{orthant} ∫ e^{−i ∑_v X_v L(w)(v)} e^{iL(w)(y_S)} u(w) dν dX`.

## The spectral shift

The Library's `θ_S(Λ) = gram(Δ_S)⁻¹ ∏_{v ∈ Δ_S} iΛ(v)` is `θ_S` at the
spectral parameter `iΛ`. `thetaShift a S Λ μ s` replaces `Λ` by `Λ + sμ`; at
`s = iτ` the spectral parameter becomes `iΛ − τμ`, with factors
`iΛ(v) − τμ(v) = τ(−μ(v)) + iΛ(v)`. Therefore, for `τ > 0` and `μ(v) ≠ 0`
for every `v ∈ Δ_S`,

```
θ_S(Λ + iτμ)⁻¹ = gram(Δ_S) · ∏_v (τ(−μ(v)) + iΛ(v))⁻¹
              = gram(Δ_S) · orthantReciprocal (−μ(v))_v τ (Λ(v))_v
              = gram(Δ_S) · orthantSign(−μ) ·
                  ∫_{−μ(v) X_v > 0} e^{−τ ∑_v (−μ(v)) X_v} e^{−i ∑_v X_v Λ(v)} dX,
```

the second line being `thetaShift_I_mul_inv` (valid for every real `τ`) and
the third `orthant_laplace` (which assumes `τ > 0` and `μ(v) ≠ 0` for every
`v ∈ Δ_S`) together with
`orthantSign(−μ)² = 1`. The Gram factor and the orientation sign are the ones
appearing in `integral_cM_exp_mul`. The case `τ = 0` is not an instance of
this display: `integral_cM_exp_mul` reaches it only through the limit of the
integrals against the test.

## Proof of `integral_cM_exp_mul`

Let `f(τ) = ∫ expShift R a y (L w) μ (iτ) · u(w) dν`, the integral of
`c_M(L(w) + iτμ)`. For `0 < τ ≤ 1` every linear factor
`L(w)(v) + iτμ(v)` has nonzero imaginary part `τμ(v)`, so
`norm_expShift_le` of `GMFamilyExponentialBound` bounds the integrand by
`expShiftBound · |u|` for every `w`. At `τ = 0` the raw sum is `cM` at `L(w)`
(`expShift_zero`), and for almost every `w` (those with `L(w)` off the walls)
the integrand converges to `c_M(L(w)) u(w)` as `τ → 0⁺`
(`continuousAt_expShift_zero`). By dominated convergence `f(τ)` tends to the
left side. For `τ > 0` each term of `expShift` is
`e^{−τμ(y_S)} · gram(S) · orthantReciprocal(−μ, τ, L(w)) · e^{iL(w)(y_S)}`, so
`f(τ)` is a finite sum of orthant reciprocal integrals; their limits are given
by `tendsto_orthantReciprocal_integral`, which uses the hypothesis that the
Fourier integrals of the phased tests are integrable on the orthants, while
`e^{−τμ(y_S)} → 1`. The two limits agree.

## Provenance

The orthant formula is the coordinate calculation of P. Delorme, *Troncature
pour les espaces symétriques réductifs*, Acta Math. 179 (1997), §9, (9.1) and
Lemma 11, printed p. 72
(`delorme-1997-reductive-symmetric-space-truncation`, SHA-256
`02eb996aa75322ecb3294cbe839dd9cc2b37077d781455e49128a2f01e0dc70c`), as
formalized in `Langlands.Analysis.ConeFourierBoundary`. Its use for `c_M` of
an exponential family replaces Lapid's convex-hull formula (E. Lapid, *On
Arthur's asymptotic inner product formula of truncated Eisenstein series*,
Clay Math. Proc. 13 (2011), §7, proof of Lemma 8, pp. 326–327,
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, volume PDF SHA-256
`760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`). The
combination with the uniform bound is a derived argument.
