# Joint absolute convergence of the real unfolded equal-rank integral

**Source.** Hervé Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §8.2, p. 55 (bottom) to p. 56 (top). There the integral (8.1) is unfolded into a double integral over the smaller quotient `N_{t+1}\GL_{t+1}` and the larger group `GL_{t+2}`, and the double integral is said to converge absolutely. This module proves that absolute convergence for the real equal-rank kernel `equalUnfoldedKernel` of `RealLocalEqualUnfolding`, which has absolute integrability of this kernel as a premise. The module is an internal supporting result.

**Difference from the source.** Jacquet (p. 55) claims that for every relatively compact set `Ω` of inducing exponents there is `A` such that (8.1) converges absolutely for `Re s ≥ A` and exponents in `Ω`. The statement here assumes instead that the real part of the separated character `d` (Jacquet's `μ_n |·|^{u_n}`) is large, i.e. dominant over the growth of `W`. Without that assumption the double integral can diverge for every `s`. Take `t = 0`, `W(h) = |h|^w` on `GL_1` with real `w`, and `Ψ` the Gaussian. Substitute `g = diag(h⁻¹, 1) x` and then `h ↦ h⁻¹`. Up to a factor depending only on `x`, the absolute `h` integral becomes `∫ e^{-π h² ‖x_1‖²} |h|^{1 + Re d - w} d^×h`, where `x_1` is the first row of `x`. This equals a constant times `‖x_1‖^{-(1 + Re d - w)}` when `1 + Re d - w > 0` and is infinite otherwise. Write `x = n(u) diag(y_1, y_2) k` with `k` orthogonal. Then `|V(x)|`, `|det x|` and the last row of `x` do not depend on `u`, while `‖x_1‖² = y_1² + u² y_2²`. So `∫ (y_1² + u² y_2²)^{-(1 + Re d - w)/2} du` diverges unless `Re d > w`, for every `s`. The equal-rank continuation must therefore start from this dominant range and reach other exponents by analytic continuation. The threshold `σ` for `Re s` does not depend on `Re d`; only the Schwartz order and the constant do.

## Statement

Write `m = t + 1` and `n = t + 2`, `G = GL_m(ℝ)`, `H = GL_n(ℝ)`, `U` for the upper unipotent subgroup of `H`, `Q` and `Q'` for the left unipotent quotients of `G` and `H`, and `Y` for real `n × n` matrices. The kernel is the published

`equalUnfoldedKernel d Ψ W V s (q, g) = Ψ(g) · V(pad(h) g) · d(det g)|det g|^{s + m/2} · W(h) · |det h|^{s - 1/2}`,

where `h = quotientRepresentative t q` is the continuous real section of `Q`. Here `d(det g)|det g|^z` is `determinantWeight d z g`. The power `|det h|^{s - 1/2}` is `ArchimedeanLocal.detPower realNormalizedAbs h (s - 1/2)`.

`RealLocalEqualJointIntegrabilityStatement t` says the following. Fix compatible real quotient data `D` of rank `t` and `D'` of rank `t+1`. Let `W : G → ℂ` and `V : H → ℂ` be continuous with real gauge estimates `RealEqualConvergence.HasGauge`. The gauge says there is `N` such that for every `M` some `C ≥ 0` gives `‖W(torus(y) k)‖ ≤ C · exp(-M · rootPos y + N Σ_j |y_j|)` for all toral coordinates `y` and orthogonal `k`. Assume also that `‖V‖` is invariant under left translation by `U`. Then there are real `ρ` and `σ` with the following property. For all real `x₀ ≥ ρ` and `y₀ > σ` there are `k : ℕ` and `C ≥ 0` such that, for every square Schwartz test `Ψ : 𝓢(Y, ℂ)`, every real character datum `d` with `Re d.exponent = x₀` and every `s` with `Re s = y₀`:

- `equalUnfoldedKernel d Ψ W V s` is integrable for `D.measure.prod D'.groupHaar`, and
- `∫ ‖equalUnfoldedKernel d Ψ W V s‖ ≤ C · sup_{(i, j) ≤ (k, 0)} SchwartzMap.seminorm ℝ i j Ψ`.

The theorem `realLocalEqualJointIntegrability` proves the statement. It is a direct application of the public theorem `exists_equalUnfoldedKernel_bound`. The module also exports `continuous_equalUnfoldedKernel`: for continuous `W` and `V` the kernel is continuous on `Q × H`. All other declarations are private helpers.

The test `Ψ` is an arbitrary square Schwartz function. It need not be the product test `equalSquareTest Φ φ` of `RealLocalEqualUnfoldingStatement`, so the result applies there with `Ψ = equalSquareSchwartz Φ φ` from `RealLocalEqualSquareFourier`. The seminorm bound is uniform in `Ψ`, `d` and `s` on the two vertical lines.

## Implemented proof

The thresholds are explicit. Let `κ, L` and `κ', L'` be the data of `exists_lintegral_alphaQ` for `D` and `D'`: the quotient integral of a function of the toral coordinate `alphaQ q` is `κ ∫ e^{L(x)} B(x) dx`. Let `N_W`, `N_V` be the gauge exponents and `P` the number of strictly upper entry positions of size `n`. Put `α = ‖L‖ + N_W + P`, `A = N_V + α + P` and `B = (A + ‖L'‖ + 1)(m + 1)`. Then `ρ = α + 1 - n/2` and `σ = B + 1/2`. For given `x₀` and `y₀` put `c = x₀ + n/2 ≥ α + 1` and `τ = y₀ - 1/2 ≥ B`.

1. *Chart.* The measurable equivalence `equalUnfoldingChart : Q' × (Q × U) ≃ᵐ Q × H` sends `(q', (q, u))` to `(q, pad(h)⁻¹ · u · h')`, where `h` and `h'` are the canonical representatives of `q` and `q'`. It swaps and reassociates the product, applies the published homeomorphism `unipotentQuotientHomeomorph (t+1)`, and then applies the skew shift `(q, g) ↦ (q, pad(h)⁻¹ g)`. It carries `D'.measure ⊗ (D.measure ⊗ D'.unipotentHaar)` to `D.measure ⊗ D'.groupHaar`. This uses `measurePreserving_unipotentQuotient` and the left invariance of `D'.groupHaar` in each fibre (`MeasurePreserving.skew_product`). So the absolute integral may be computed on `Q' × (Q × U)`, where the iterated lower integral `lintegral_prod_le` bounds the product lower integral.
2. *Size at the chart.* The test depends only on the first `m` rows and the last row. Left multiplication by `pad(h)⁻¹` and by `u` does not change the last row, and `det u = 1`. Each representative is `torus(alphaQ q) · k` with `k` orthogonal (`quotientRepresentative_eq_torus`), so `|det h| = exp Σ alphaQ q`. Using also the invariance of `‖V‖` under `U`, `norm_kernel_chart` computes the absolute value of the kernel at `(q', (q, u))` exactly. It is `‖Ψ(pad(h)⁻¹ u h')‖ · ‖V(h')‖ e^{(Re d + Re s + m/2) Σ alphaQ q'} · ‖W(h)‖ e^{-(Re d + n/2) Σ alphaQ q}`.
3. *Schwartz split.* `norm_schwartz_le_split` bounds `‖Ψ(g)‖` by `2^{K₁+K₂}` times the seminorm supremum of order `(K₁ + K₂, 0)`, times `(1 + ‖first m rows of g‖)^{-K₁} (1 + ‖last row of g‖)^{-K₂}`. Conjugating the first rows by the orthogonal parts changes the norm by at most the factor `m n` (sup operator norm, entries of orthogonal matrices bounded by `1`). In coordinates the first rows become the matrix of entries `e^{-η_i} u_{i,j} e^{y_j}`, with `η = alphaQ q` and `y = alphaQ q'`. Its diagonal entries and strictly upper entries bound the decay weight (`inv_one_add_norm_pow_le`): with `K₁ = (m + P) K` it is at most `(m n)^{K₁} ∏_i (1 + e^{y_i - η_i})^{-K} ∏_{p=(i,j)} (1 + e^{y_j - η_i} |u_{i,j}|)^{-K}`. This gives the pointwise majorant `norm_kernel_chart_le`.
4. *The `U` integral.* Every Haar measure on `U` is a multiple of `upperStepHaar (t+1) 1`, which is the product of self-dual Lebesgue measures on the strictly upper entries. For `K ≥ 2`, `∫ (1 + e^{l} |v|)^{-K} dv = e^{-l} ∫ (1 + |v|)^{-K} dv` (`integral_entry_decay`). Hence `exists_lintegral_unipotent_decay` integrates the product of entry weights to `C₀ · exp(-Σ_p l_p)` with `C₀ < ∞`. With `l_p = y_j - η_i` this removes `u` and leaves the factor `e^{-Σ_p y_j} e^{Σ_p η_i}`.
5. *The `Q` integral.* For fixed `y`, `lintegral_quotient_bound` bounds the remaining integral over `Q`. Its integrand is `‖W(h)‖ e^{-c Σ η} ∏_i (1 + e^{y_i - η_i})^{-K} e^{Σ_p η_i}`. The bound is `κ · CW e^{α Σ_j |y_j| - c Σ_{i<m} y_i} · ∫ e^{-Σ|x_i|} dx`. The proof uses the gauge of `W` with `M = 0`, then `exists_lintegral_alphaQ`, then translation of Lebesgue measure by the first `m` coordinates `z` of `y` (`lintegral_add_right_eq_self`). After the translation `η = x + z`, each coordinate gives `e^{α|x_i| - c x_i} (1 + e^{-x_i})^{-K} ≤ e^{-|x_i|}` (`coord_decay`). For `x_i ≥ 0` this uses `c ≥ α + 1`; for `x_i < 0` it uses `K ≥ α + c + 1`. Here dominance of `Re d` is used. `lintegral_inner_le` combines steps 4 and 5 for a fixed larger class `q'`.
6. *The `Q'` integral.* What remains is a function `Fo` on `Q'`: `‖V(h')‖`, times `e^{(x₀ + y₀ + m/2) Σ y}`, times `(1 + ‖last row of h'‖)^{-K₂}`, times `e^{-Σ_p y_j} · CW e^{α Σ|y_j| - c Σ_{i<m} y_i}`, with `y = alphaQ q'`. The exponents rearrange to `e^{c y_n} · e^{τ Σ y + α Σ|y| - Σ_p y_j}`. The last row of `torus(y) k` has norm at least `e^{y_n}/(m+1)` (`RealEqualConvergence.exp_le_mul_norm_lastRow`). So with `K₂ ≥ c + Mo`, `exp_mul_inv_lastRow_le` absorbs `e^{c y_n}` and leaves `(m+1)^{K₂} e^{-Mo max(y_n, 0)}`. The gauge of `V` at order `Mo = ⌈B + τ(m+1)⌉` then bounds `Fo` by `CV · CW (m+1)^{K₂} exp(-Mo · rootPos y + A Σ|y| + τ Σ y - Mo max(y_n, 0))`. `RealEqualConvergence.integrable_of_toral_bound` turns this into integrability of the continuous function `Fo`, since `τ ≥ B`.
7. *Conclusion.* The chained bounds give `∫⁻ ‖kernel‖ ≤ S · R₀`. Here `S` is the seminorm supremum of order `k = (m + P) K + K₂`, with `K = max 2 ⌈α + c + 1⌉` and `K₂ = ⌈c + Mo⌉`. `R₀ < ∞` collects `2^k (m n)^{(m+P)K}`, `C₀`, `κ`, `∫ e^{-Σ|x_i|}` and `∫ Fo`. The kernel is continuous (`continuous_equalUnfoldedKernel`), hence strongly measurable. A finite lower integral of its norm gives integrability, and `C = R₀.toReal` gives the stated bound.

## Scope

This module proves only joint absolute convergence, with a seminorm bound, for exponents whose separated character is dominant and with `Re s` beyond a threshold. It does not assume or prove the Whittaker law, unfolding identities, meromorphic continuation or functional equations, and it does not prove `RealLocalUniformPositiveEqualContinuationStatement`. Non-dominant exponents are not covered.

## Uniform abscissas

`RealLocalEqualUniformJointIntegrabilityStatement` fixes the growth
exponents in the smaller toral bound and the larger simple-root gauge
before choosing the leading and spectral abscissas. For those exponents,
the same abscissas apply to all continuous functions with the indicated
bounds and with invariant absolute value of the larger function under the
upper unipotent group. The smaller function needs only its toral growth
bound. The seminorm order and integral bound may depend on the functions
and the two real parts. In the proof the abscissas use the two exponents
and the toral densities. The constants of the two function bounds enter
after that choice. This is a uniform form of the estimates for the
unfolded kernel of Jacquet, §8.1, equation (8.1).
