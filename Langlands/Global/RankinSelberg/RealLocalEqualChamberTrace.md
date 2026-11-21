# Interval bounds and holomorphy of the real unfolded equal-rank integral

**Source.** Hervé Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §8.2, pp. 55–57. There the integral (8.1) is unfolded into a double integral over the smaller quotient `N_{t+1}\GL_{t+1}` and the larger group `GL_{t+2}`. It is then compared with finite sums of products of lower-rank integrals and continued analytically. This module supplies the analytic properties of the real unfolded double integral that such a comparison needs. They are uniform bounds over intervals of the separated exponent, holomorphy in both exponents, and extension of identities from a deep chamber by uniqueness of analytic continuation. It is an internal supporting result. It is the real analogue of the published complex modules `ComplexLocalEqualChamberTrace` and `ComplexLocalEqualSquareTraceBounds`. It builds on the joint absolute convergence theorem `realLocalEqualJointIntegrability` of `RealLocalEqualJointIntegrability`.

## Notation

Write `m = t + 1` and `n = t + 2`, `G = GL_m(ℝ)`, `H = GL_n(ℝ)`, `U` for the upper unipotent subgroup of `H`, `Q` for the left unipotent quotient of `G`, and `Y` for real `n × n` matrices. The kernel is the published

`equalUnfoldedKernel d Ψ W V s (q, g) = Ψ(g) · V(pad(h) g) · d(det g)|det g|^{s + m/2} · W(h) · |det h|^{s - 1/2}`,

where `h = quotientRepresentative t q`. The measure on `Q × H` is `D.measure.prod D'.groupHaar` for compatible real quotient data `D` of rank `t` and `D'` of rank `t + 1`. The real character datum `charData p z` (from `RealJacquetFrobenius`) is the character `x ↦ (x/|x|)^p |x|^z` with parity `p : Fin 2` and exponent `z`. Its exponent is `z`.

The standing hypotheses on `W : G → ℂ` and `V : H → ℂ` are the hypotheses of `RealLocalEqualJointIntegrabilityStatement`. Both are continuous and satisfy the real gauge estimate `RealEqualConvergence.HasGauge`, and `‖V(u g)‖ = ‖V(g)‖` for every `u ∈ U`.

## Declarations

- `norm_equalUnfoldedKernel_le_endpoints d₁ d₂ d`. Let `Re d₁.exponent ≤ Re d.exponent ≤ Re d₂.exponent`. Then at every point of `Q × H` the norm of the kernel at `d` is at most the sum of the norms of the kernels at `d₁` and `d₂`, for the same `Ψ, W, V, s`. This holds for arbitrary functions `Ψ`, `W`, `V`.
- `RealLocalEqualChamberTraceStatement t` (a `Prop`) and its proof `realLocalEqualChamberTrace`. Under the standing hypotheses there are real `ρ` and `σ` with the following property. For all real `x₁ ≥ ρ`, all `x₂` and all `y > σ` there is a continuous function `weight : 𝓢(Y, ℂ) → ℝ` with `weight 0 = 0`. For every square Schwartz test `Ψ`, every real character datum `d` with `x₁ ≤ Re d.exponent ≤ x₂` and every `s` with `Re s = y`, the kernel `equalUnfoldedKernel d Ψ W V s` is integrable. Its absolute integral is at most `weight Ψ`.
- `equalUnfoldedKernel_charData`. At the character `charData p u` the kernel equals `Ψ(g) V(pad(h) g) (det g/|det g|)^p W(h)` times the single exponential `exp((u + s + m/2) log|det g| + (s - 1/2) log|det h|)`.
- `differentiableOn_integral_equalUnfoldedKernel_affine`. Fix the parity `p`, base points `u₀, s₀ ∈ ℂ` and real slopes `c₁, c₂`. Let `S ⊆ ℂ` be open and suppose the kernel at `(charData p (u₀ + c₁ w), s₀ + c₂ w)` is integrable for every `w ∈ S`. Then `w ↦ ∫ equalUnfoldedKernel (charData p (u₀ + c₁ w)) Ψ W V (s₀ + c₂ w)` is holomorphic on `S`. This holds for arbitrary functions `Ψ`, `W`, `V`.
- `eq_mul_integral_equalUnfoldedKernel_of_deep`. Let `F, N : ℂ × ℂ → ℂ` be differentiable everywhere. Suppose the kernel at `(charData p z, s)` is integrable whenever `Re z > τ` and `Re s > σ`. Suppose also that `F(z, s) = N(z, s) · ∫ equalUnfoldedKernel (charData p z) Ψ W V s` holds whenever `Re z > τ'` and `Re s > σ'`, for some `τ'` and `σ'`. Then this identity holds whenever `Re z > τ` and `Re s > σ`.
- `equalNormalizedTrace D D' p A B c W V Ψ z s` (a definition). It is `c · (A(s) · B(s + z) · ∫ equalUnfoldedKernel (charData p z) Ψ W V s)`, for functions `A, B : ℂ → ℂ` and a constant `c`. It is the unfolded integral multiplied by normalizing factors in `s` and `s + z`, such as the inverse lower and upper `L`-factors in the later comparison.
- `exists_equalNormalizedTrace_bound`. Assume the standing hypotheses, a parity `p` and a constant `c`. Let `A` and `B` be continuous with `HasStripExponentialGrowth` (from `GammaStripGrowth`: on every vertical strip, `‖A(s)‖ ≤ C e^{K |Im s|}` once `|Im s| ≥ T`). Then there are real `τ` and `σ` with the following property. For all real `l ≥ τ`, all `u` and all `y > σ` there are `K, L ≥ 0` and a continuous `w : 𝓢(Y, ℂ) → ℝ` with `w 0 = 0` such that

  `‖equalNormalizedTrace … Ψ₁ z s - equalNormalizedTrace … Ψ₂ z s‖ ≤ w(Ψ₁ - Ψ₂) · exp(K |Im s| + L |Im z|)`

  for all square Schwartz tests `Ψ₁, Ψ₂` and all `z, s` with `l ≤ Re z ≤ u` and `Re s = y`.

All other declarations are private helpers.

## Implemented proof

*Endpoint bound.* Only the factor `|det g|^{Re d + Re s + m/2}` of the absolute kernel depends on `d`. If `|det g| ≥ 1` it is increasing in `Re d`, so it is bounded by its value at `d₂`. Otherwise it is decreasing, and it is bounded by its value at `d₁`. The other factors agree, so the norm at `d` is bounded by one of the two endpoint norms (`Real.rpow_le_rpow_of_exponent_le` and `Real.rpow_le_rpow_of_exponent_ge`).

*Interval bound.* Take `ρ` and `σ` from `realLocalEqualJointIntegrability`. Given `x₁ ≥ ρ`, `x₂` and `y > σ`, put `x₂' = max x₁ x₂`. That theorem gives `(k₁, C₁)` for the vertical line `Re d = x₁` and `(k₂, C₂)` for `Re d = x₂'`. Apply it to the endpoint characters `e₁ = charData 0 x₁` and `e₂ = charData 0 x₂'`. Write `S_k(Ψ) = Σ_{(i,j) ≤ (k,0)} SchwartzMap.seminorm ℝ i j Ψ`. This finite sum of continuous seminorms is continuous on `𝓢(Y, ℂ)` (`schwartz_withSeminorms`) and dominates the seminorm supremum (`Seminorm.finset_sup_apply_le`). The weight is `C₁ S_{k₁} + C₂ S_{k₂}`, which vanishes at `0`. The kernel at `d` is continuous (`continuous_equalUnfoldedKernel`), hence strongly measurable. By the endpoint bound it is dominated by the sum of the two integrable endpoint norms, so it is integrable. Integrating the endpoint bound gives the estimate.

*Exponential form and holomorphy.* `equalUnfoldedKernel_charData` unfolds `charData_character_apply` and writes each power `|x|^z` as `exp(z log|x|)` (`Complex.cpow_def_of_ne_zero` with `Complex.ofReal_log`). Along an affine line, the kernel at `(charData p (u₀ + c₁ w), s₀ + c₂ w)` is therefore the kernel at `(charData p u₀, s₀)` times `exp(w L(q))`. Here `L(q, g) = (c₁ + c₂) log|det g| + c₂ log|det h|` is a measurable real function. Measurability uses continuity of the section `quotientRepresentative` (from `unipotentQuotientHomeomorph`) and of the determinant. Holomorphy then follows from the published `differentiableOn_integral_mul_cexp` (`ComplexLocalEqualHolomorphy`): an integral of `A(q) exp(w B(q))` is holomorphic on any open set of `w` on which it converges absolutely.

*Extension from the deep chamber.* Slope `(1, 0)` gives holomorphy in `z` on `Re z > τ` for each `s` with `Re s > σ`. Slope `(0, 1)` gives holomorphy in `s` on `Re s > σ` for each `z` with `Re z > τ`. First fix `s` with `Re s > max σ σ'`. Both sides are holomorphic in `z` on `Re z > τ` and agree for `Re z > τ'`, so they agree on the whole half-plane (`eqOn_halfPlane` from `LandauMellin`, uniqueness of analytic continuation on a connected open half-plane). Then fix `z` with `Re z > τ`. Both sides are holomorphic in `s` on `Re s > σ` and agree for `Re s > max σ σ'` by the first step, so they agree for all `Re s > σ`.

*Normalized trace bound.* A continuous function with `HasStripExponentialGrowth` is bounded on the compact part `|Im| ≤ max T 0` of each strip. So on every closed strip it satisfies `‖F(z)‖ ≤ C e^{K |Im z|}` for all `z` in the strip (private `norm_le_all_strip_of_stripGrowth`). Apply this to `A` on the line `Re = y` and to `B` on the strip `y + l ≤ Re ≤ y + u`. The kernel is additive in the Schwartz test, so the difference of the two integrals is the integral for `Ψ₁ - Ψ₂`. Its norm is at most `weight(Ψ₁ - Ψ₂)` by the interval bound. Here `weight` is the interval-bound weight for `x₁ = l` and `x₂ = u`, using `Re (charData p z).exponent = Re z`. Since `|Im(s + z)| ≤ |Im s| + |Im z|`, the claim holds with `w = ‖c‖ C_A C_B · weight` and exponents `K_A + K_B` for `|Im s|` and `K_B` for `|Im z|`.

## Scope

This module proves no unfolding identity, finite-product comparison, continuation of the equal-rank integral, functional equation or `RealLocalUniformPositiveEqualContinuationStatement`. All bounds hold only in the dominant range `Re d ≥ ρ` of the joint integrability theorem. Below that range the double integral can diverge (see `RealLocalEqualJointIntegrability.md`).
