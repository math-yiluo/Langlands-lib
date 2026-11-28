# Exponential decay on cones from cone shift equations

Module `Langlands.Global.AdelicConeShiftEquationDecay`, namespace
`Langlands.Global.ConeShiftDecay`.

Throughout, `(T, i, ν, T₀, j)` is an algebraic Siegel setup (`IsSiegelAlgebraicSetup`) of a
connected reductive `G` over a number field `F`, `Δ = simpleRelativeRoots i ν`, `A_{T₀}` is the
positive torus `PositiveRealTorus.intrinsicSubgroup F T₀`, `a(b) = positiveMap F G T i T₀ j b`,
`log |χ(b)| = logNormHom F T₀ b (j ≫ χ)`, `δ(b) = siegelModulus F G T i ν T₀ j b`,
`σ = adelicLogHeight F G rho` and `A_G = RestrictionSplitCentre.canonicalSubgroup F G`.

## Main result

`exists_coneBound`: let `J ⊆ Δ`, let `α₀ ∈ Δ \ J`, let `δ, ε > 0`, `m : ℕ`, `B : ℝ`, let
`t' ≤ t` and `t' ≤ 1` be thresholds and `Ω ⊆ G(𝔸)` compact. There is `B'` such that every
`f : G(𝔸) → ℂ` with

1. `‖f(z g)‖ = ‖f(g)‖` for `z ∈ A_G` and `g ∈ G(𝔸)`,
2. `‖f(a(b) ω)‖ ≤ B δ(b)^{1/2} σ(a(b) ω)^m` for `b` in the weak simple-root chamber of threshold
   `t'` and `ω ∈ Ω`, and
3. `HasConeShiftEquations F G T i ν T₀ j J δ ε m f` (module
   `Langlands.Global.AdelicEisensteinWeakConstantTermRemainderStatement`)

satisfies `‖f(z a(b) ω)‖ ≤ B' δ(b)^{1/2} e^{−(εδ/4) R}` for `z ∈ A_G`, `b` in the weak chamber of
threshold `t`, `ω ∈ Ω` and every real `R` with `|log |β(b)|| ≤ R` for all `β ∈ Δ` and
`δ R ≤ log |α(b)|` for all `α ∈ Δ \ J`. The constant `B'` depends only on the data listed before
`f`, not on `f`.

## Auxiliary results

- `exists_logNormHom_eq`: for every function `s` on the characters of `T` there is `y ∈ A_{T₀}`
  with `log |β(y)| = s(β)` for every `β ∈ Δ`. The fundamental rays `r_α` of the Library's
  `StandardParabolicFamily.exists_siegelFundamentalRays` (for the standard parabolic family
  `StandardParabolicFamily.ofMaximalSplitTorus` of the setup) have `log |α(r_α)| > 0` and
  `log |β(r_α)| = 0` for `β ≠ α`. The functional
  `ℓ = ∑_α (s(α) / log |α(r_α)|) · characterLog(r_α)` on the characters of `T₀` takes the value
  `s(β)` at `j ≫ β`, and `PositiveRealTorus.exists_characterLog_eq` gives a positive point of
  the split torus `T₀` with logarithm `ℓ`.
- `logNormHom_mul`, `logNormHom_one`, `logNormHom_pow`, `logNormHom_inv`: `log |χ(·)|` is a
  homomorphism from the points of `T₀` to `ℝ`.
- `coe_finprod_nnreal`: the coercion `ℝ≥0 → ℝ` commutes with `finprod`.
- `exists_siegelModulus_eq_exp`: there are `e : Δ → ℕ` with
  `δ(b) = exp(∑_α e_α log |α(b)|)` for all `b ∈ A_{T₀}`. This is the Library's
  `AdelicSiegelFactors.exists_simpleRoot_exponents` with logarithms taken.
- `exists_adelicLogHeight_le`: for compact `Ω` there is `c ≥ 0` with
  `σ(a(y) ω) ≤ c (1 + R)` whenever `|log |β(y)|| ≤ R` for all `β ∈ Δ` and `ω ∈ Ω`. If `rho` has
  size `0`, then `GL_0(𝔸)` is trivial and `σ` is constant. Otherwise the restricted simple roots
  span `X^*(T₀) ⊗ ℚ` (`AdelicSiegelFactors.ratSpan_restrict_simpleRelativeRoots_eq_top`, with
  the Library's `relativeRootNegation` and `relativeCharacterRootComplement`), so
  `RepresentationGrowth.adelicPositiveTorusLogHeightBound` gives `H(a(y)) ≤ C e^{rR}` for the
  adelic height `H`. Submultiplicativity (`adelicHeight_mul_le`), a bound for `H` on `Ω` and
  `max(1, ‖·‖) ≤ H` (from `adelicHeight_eq_scalar_mul_sourceNorm`) give
  `σ(a(y) ω) ≤ 1 + log C + rR + log max(1, sup_Ω H)`.
- `sqrt_exp`: `√(e^a) = e^{a/2}`.
- `one_add_pow_le_exp`: `(1 + R)^m ≤ e^{m a (1 + R)} / a^m` for `a > 0` and `R ≥ 0`, from
  `a(1 + R) ≤ e^{a(1 + R)}`.

## Proof of `exists_coneBound`

Write `ℓ(β) = log |β(b)|`, `N = 2m + 1` and `Lm(x) = ∑_α e_α log |α(x)|`, so that
`δ(x)^{1/2} = e^{Lm(x)/2}`. The hypotheses give `R ≥ 0` and `ℓ(α₀) ≥ δR ≥ 0`.

1. By hypothesis 1, `‖f(z a(b) ω)‖ = ‖f(a(b) ω)‖`.
2. `exists_logNormHom_eq` gives `y ∈ A_{T₀}` with `log |β(y)| = 0` for `β ∈ J` and
   `log |α(y)| = ℓ(α)/N` for `α ∈ Δ \ J`. Put `b₀ = y^{-N} b`. For every `q`,
   `log |χ(y^q b₀)| = log |χ(b)| + (q − N) log |χ(y)|` and
   `Lm(y^q b₀) = Lm(b) + (q − N) Lm(y)`.
3. The point `y` satisfies the conditions of `HasConeShiftEquations`: `ℓ(α) ≥ δR ≥ 0` for
   `α ∉ J`, and `δ ℓ(α') ≤ δR ≤ ℓ(α)`. So there are `w_0, …, w_{m-1}` with
   `|w_k| ≤ κ = e^{Lm(y)/2 − ε ℓ(α₀)/N}` (the bound for `α = α₀`), and `∏_k (L_{a(y)} − w_k)`
   annihilates `f`.
4. For `q < m`, the point `y^q b₀` has `log |β(y^q b₀)| = ℓ(β)` for `β ∈ J` and
   `log |α(y^q b₀)| = ℓ(α) q/N ∈ [0, ℓ(α)]` for `α ∉ J`. It lies in the weak chamber of threshold
   `t'`, because `log t' ≤ log t ≤ ℓ(β)` and `log t' ≤ 0`, and all its simple-root logarithms are
   at most `R` in absolute value. Hypothesis 2 and `exists_adelicLogHeight_le` give
   `‖f(a(y)^q a(b₀) ω)‖ ≤ max(B, 0) e^{Lm(y^q b₀)/2} (c(1 + R))^m ≤ κ^q M` with
   `M = e^{ε m ℓ(α₀)/N} max(B, 0) e^{(Lm(b) − N Lm(y))/2} (c(1 + R))^m`, since
   `ε q ℓ(α₀)/N ≤ ε m ℓ(α₀)/N`.
5. `Langlands.Analysis.norm_le_of_translationSolution` (module
   `Langlands.Analysis.ShiftRecurrenceBound`), applied to the sequence
   `q ↦ f(a(y)^q a(b₀) ω)`, gives at `q = N`, where `a(y)^N a(b₀) = a(b)`:
   `‖f(a(b) ω)‖ ≤ 3^m (N + 1)^m κ^N M
   = 3^m (N + 1)^m e^{Lm(b)/2 − ε ℓ(α₀) + ε m ℓ(α₀)/N} max(B, 0) (c(1 + R))^m`.
6. Since `m/N ≤ 1/2` and `ℓ(α₀) ≥ δR`, the exponent is at most `Lm(b)/2 − εδR/2`. With
   `κ_c = εδ / (4(m + 1))`, `one_add_pow_le_exp` and `m κ_c ≤ εδ/4` give
   `(1 + R)^m ≤ e^{εδ/4} e^{εδR/4} / κ_c^m`. Hence
   `‖f(a(b) ω)‖ ≤ B' e^{Lm(b)/2} e^{−εδR/4}` with
   `B' = 3^m (N + 1)^m max(B, 0) c^m e^{εδ/4} / κ_c^m`.

The proof uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Source

P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
`delorme-2023-spectral-theorem-langlands` (published PDF): proof of Lemma 5.1, pp.18–19, and
Lemma 5.2 with its proof, p.19. Delorme applies Lapid's Lemma 3 (E. Lapid, *On Arthur's
asymptotic inner product formula of truncated Eisenstein series*, 2011, printed p.317, registered
as `lapid-2011-asymptotic-inner-product-truncated-eisenstein`) to the normalized exponential
polynomials `t ↦ e^{−tρ(Y)} (φ_Q − φ^w_Q)(exp X exp tY ω)` along the rays of the cone
`𝔞^{G,+}_{Q,δ}`, with the bound (5.1) near the origin of each ray, and then passes from
`exp X exp Y` (`X ∈ 𝔞_0^+`, `Y` in the cone) to the cone `𝔞^{G+}_{0,Q,δ}` of `𝔞_0` in Lemma 5.2.
Here the ray from `b₀` through `b` is followed in `N` equal steps along a point `y` of
`𝔄_Q ∩ A_{T₀}`, and the difference equation along `y` replaces the exponential polynomial: its
roots have absolute value at most `δ(y)^{1/2} e^{−ε log |α₀(y)|}`, and the bound for linear
recurrences replaces Lapid's Lemma 3. The starting points `y^q b₀` (`q < m`) lie halfway or
less along the ray, in the region where the polynomial bound (5.1) applies; the decay gained
along the second half of the ray absorbs the polynomial factor. The central factor `z` is removed
by the unitary central character, as in Delorme's treatment of `𝔞_G`.
