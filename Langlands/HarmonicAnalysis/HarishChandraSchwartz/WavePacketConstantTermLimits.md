# The limits in the proof of Proposition VI.4.1 (constant terms of wave packets)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.WavePacketConstantTermLimits`,
namespace `Langlands.HarishChandraSchwartz`. It imports only Mathlib
(`MeasureTheory.Integral.DominatedConvergence`, `MeasureTheory.Integral.Bochner.Set`,
`Analysis.SpecialFunctions.Pow.Continuity`) and uses `setIntegral_map_equiv`,
`integral_smul_measure`, `tendsto_setIntegral_of_monotone`,
`tendsto_integral_filter_of_dominated_convergence`, `tendsto_finsetSum`,
`Real.continuousAt_const_rpow` and `Real.rpow_le_rpow_of_exponent_ge'`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`), proof of Proposition VI.4.1. Printed page
numbers; the PDF page is the printed page minus 234. The quotes from pages 307 and 313 were
checked on the rendered PDF pages 73 and 79.

- Formula (1), printed p. 307 (PDF p. 73): "Fixons `a ∈ A_{M'}` tel que `|α(a)|_F < 1` pour tout
  `α ∈ Σ(P')`. Pour `n ∈ ℕ`, posons `U'_n = a^{−n}(H ∩ U')a^n`. Par définition,
  `f_ψ^{(P')}(m') = δ_{P'}(m')^{1/2} ∫_{U'} f_ψ(m'u') du' = δ_{P'}(m')^{1/2} lim_{n→∞}
  ∫_{U'_n} f_ψ(m'u') du' = δ_{P'}(m')^{1/2} lim_{n→∞} δ_{P'}(a)^{−n} ∫_{H∩U'}
  f_ψ(m' a^{−n} u' a^n) du'`. (1)"
- Printed p. 310 (PDF p. 76): "Pour `ε ⩾ 0`, posons `X^w(ε) = ∫_{U'} δ_{P̄'}(m_{P̄'}(u))^{(1/2)+ε}
  e(u') du'`. Grâce au Lemme II.3.4, cette intégrale est absolument convergente, uniformément en
  `ε`. La fonction `X^w` est donc continue en `0`." and (7):
  "`X^w_s(ε) = ∫_O ∫_{U'} δ_{P̄'}(m_{P̄'}(u'))^{1/2+ε} µ(ω)[e(s, ω, u')](m m_{P̄'}(u')) du' dω`",
  with `X^w(ε) = Σ_{s ∈ W(G|M)} X^w_s(ε)`.
- Assertion (8), printed p. 311 (PDF p. 77): "Notons `Y_s(ω, ε)` l'intégrale intérieure […]
  il existe `ε₀` tel que `Y_s` soit bornée sur `O × ]0, ε₀[`; pour presque tout `ω ∈ O`,
  `lim_{ε→0} Y_s(ω, ε) = γ(G|M) c(G|M)² E^M_M[(°c_{P'|P}(s, ω)ψ_ω)(1, 1)](m)`. En admettant
  cela, et en utilisant les égalités `f_ψ^{(P')}(m) = X^w = lim_{ε→0} X^w(ε) = lim_{ε→0}
  Σ_{s ∈ W(G|M)} X^w_s(ε)`, on obtient l'égalité (ii)".
- Printed pp. 312–313 (PDF pp. 78–79): `ζ(λ, ε) = Π_{α ∈ Σ_red(P)} [⟨λ, α̌⟩^{n(α)/2}
  ⟨λ + 2εs^{−1}ρ, α̌⟩^{−n(α)/2}]`, `Y(χ_λ, ε) = ζ(λ, ε) y(λ, ε)` with `y` continuous, "Mais la
  fonction `ζ` est bornée sur `ia_M^* × ℝ` car pour tout `(λ, ε) ∈ ia_M^* × ℝ` et tout
  `α ∈ Σ_red(P)`, `|⟨λ, α̌⟩| ⩽ |⟨λ + 2εs^{−1}ρ, α̌⟩|`. La fonction `Y` est donc bornée".

The abstraction, the hypotheses and the proof route are internal to this project.

## Relation to the source

- `tendsto_inv_mul_setIntegral_comp` is formula (1) for an integrable `F` on a measurable space
  `U` (for Waldspurger `F(u') = f_ψ(m'u')` on `U'`): `e_n` are measurable bijections with
  `e_n(μ) = c_n μ` (for Waldspurger `e_n(u') = a^{−n} u' a^n` and `c_n = δ_{P'}(a)^n`, so that
  `U'_n = e_n(H ∩ U')`), the sets `e_n(H)` increase and exhaust `U`; these properties of the
  conjugations (the modulus `δ_{P'}`, the contraction by `a`) are hypotheses. The integrability of
  `u' ↦ f_ψ(m'u')` is a hypothesis (Proposition II.4.5 for `f_ψ ∈ 𝒞(G)`).
- `zetaFactor` is `ζ(λ, ε)` with `z_α = ⟨λ, α̌⟩`, `b_α = ⟨2εs^{−1}ρ, α̌⟩` and `k_α = n(α)/2`
  (Lean's `x / 0 = 0` covers the points where a denominator vanishes);
  `norm_zetaFactor_le_one` is its boundedness. The factorization `Y = ζ y`, the continuity of `y`
  (from the intertwining operators and `µ`), and the limit (10) are not part of this module.
- `tendsto_integral_rpow_add_mul` is the continuity of `X^w(ε)` at `0`, for a function `δ ≥ 0`
  (for Waldspurger `u' ↦ δ_{P̄'}(m_{P̄'}(u'))`) and `e`, under the integrability of
  `(δ^{1/2} + δ^{1/2+ε₀}) |e|` (in the source, Lemma II.3.4), which dominates `δ^{1/2+ε} |e|` for
  `0 < ε < ε₀`.
- `eq_sum_integral_of_tendsto` is the conclusion of the proof of (ii) from (8): the bounds and
  the almost-everywhere limits of the `Y_s` are hypotheses, as are the equality
  `X^w(ε) = Σ_s X^w_s(ε)` (from Proposition V.1.1 and (6)) and the limit `X^w(ε) → X^w`
  (`tendsto_integral_rpow_add_mul`). The orbit carries a finite measure.
- The functions `E^G_P ψ_ω`, the weak constant terms, `µ`, `j`, `γ(G|M)`, `c(G|M)` and the
  intertwining operators do not occur: they enter only through the hypotheses.

## Contents

- `tendsto_inv_mul_setIntegral_comp`: for a measurable space `U` with a measure `μ`, a real
  normed space `E`, `F : U → E` with `hF : Integrable F μ`, `H : Set U` with
  `hH : MeasurableSet H`, `e : ℕ → U ≃ᵐ U`, `c : ℕ → ℝ≥0∞` with `hc0 : ∀ n, c n ≠ 0`,
  `hctop : ∀ n, c n ≠ ∞`, `hmap : ∀ n, Measure.map (e n) μ = c n • μ`,
  `hmono : Monotone fun n => e n '' H` and `hcover : ⋃ n, e n '' H = Set.univ`:
  `(c n).toReal⁻¹ • ∫ v in H, F (e n v) ∂μ` tends to `∫ u, F u ∂μ`.
- `norm_div_add_ofReal_le_one`: for `z : ℂ` with `hz : z.re = 0` and `b : ℝ`,
  `‖z / (z + b)‖ ≤ 1`.
- `zetaFactor s z b k` (definition), for a finite set `s` of indices, `z : ι → ℂ`, `b : ι → ℝ`,
  `k : ι → ℕ`: `∏ i ∈ s, (z i / (z i + b i)) ^ k i`.
- `norm_zetaFactor_le_one`: if `(z i).re = 0` for `i ∈ s`, `‖zetaFactor s z b k‖ ≤ 1`.
- `tendsto_integral_rpow_add_mul`: for `δ : U → ℝ` with `hδ0 : ∀ u, 0 ≤ δ u` and
  `hδm : Measurable δ`, `e : U → ℂ` with `hem : AEStronglyMeasurable e μ`, `ε₀` with
  `hε₀ : 0 < ε₀` and `hint : Integrable (fun u => (δ u ^ (1/2) + δ u ^ (1/2 + ε₀)) * ‖e u‖) μ`:
  `ε ↦ ∫ u, (δ u ^ (1/2 + ε) : ℂ) * e u ∂μ` tends to `∫ u, (δ u ^ (1/2) : ℂ) * e u ∂μ` as
  `ε → 0⁺` (`𝓝[>] 0`).
- `eq_sum_integral_of_tendsto`: for a measurable space `Ω` with `[IsFiniteMeasure ν]`, a finite
  set `S`, `Y : ι → Ω → ℝ → ℂ`, `F : ι → Ω → ℂ`, `ε₀ C` with `hε₀ : 0 < ε₀`,
  `hmeas : ∀ i ∈ S, ∀ ε, AEStronglyMeasurable (fun ω => Y i ω ε) ν`,
  `hbound : ∀ i ∈ S, ∀ ω ε, ε ∈ Set.Ioo 0 ε₀ → ‖Y i ω ε‖ ≤ C`,
  `hlim : ∀ i ∈ S, ∀ᵐ ω ∂ν, Tendsto (Y i ω) (𝓝[>] 0) (𝓝 (F i ω))`, `X : ℝ → ℂ`, `T : ℂ`,
  `hX : ∀ ε ∈ Set.Ioo 0 ε₀, X ε = ∑ i ∈ S, ∫ ω, Y i ω ε ∂ν` and
  `hT : Tendsto X (𝓝[>] 0) (𝓝 T)`: `T = ∑ i ∈ S, ∫ ω, F i ω ∂ν`.

## Proof

`tendsto_inv_mul_setIntegral_comp`: by `setIntegral_map_equiv` and `hmap`,
`c_n ∫_{e_n(H)} F = ∫_H F ∘ e_n` (using `e_n⁻¹(e_n(H)) = H`), so the sequence is
`∫_{e_n(H)} F dμ`, which tends to `∫_{⋃ e_n(H)} F = ∫_U F` (`tendsto_setIntegral_of_monotone`).

`norm_div_add_ofReal_le_one`: if `z + b = 0` the quotient is `0`; otherwise
`|z|² = (Im z)² ≤ b² + (Im z)² = |z + b|²`. `norm_zetaFactor_le_one`: a product of factors of
norm at most `1` (`Finset.prod_le_one₀`).

`tendsto_integral_rpow_add_mul`: dominated convergence on `𝓝[>] 0`. For `0 < ε < ε₀`,
`δ^{1/2+ε} ≤ δ^{1/2}` where `δ ≤ 1` and `δ^{1/2+ε} ≤ δ^{1/2+ε₀}` where `δ ≥ 1`, so
`|δ^{1/2+ε} e| ≤ (δ^{1/2} + δ^{1/2+ε₀}) |e|`; and `ε ↦ δ(u)^{1/2+ε}` is continuous at `0`
(`Real.continuousAt_const_rpow` when `δ(u) ≠ 0`, constant `0` near `0` when `δ(u) = 0`).

`eq_sum_integral_of_tendsto`: dominated convergence (constant bound `C`, integrable since `ν` is
finite) gives `∫ Y_s(·, ε) → ∫ F_s` for each `s`, hence the sum converges to
`Σ_s ∫ F_s`; `X` agrees with the sum on `]0, ε₀[`, so the two limits coincide
(`tendsto_nhds_unique`).
