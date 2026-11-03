# The `K × K`-averaging estimate of Proposition VIII.3.1

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConjugationBound`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalBounds`, for `XiUpperBound`
(the upper bound of Lemma II.1.1 as a Prop). Through it, it uses the published modules
`Convolution` (`ConvolutionWeights`, `enorm_le_nu_mul`), `Basic` (`nu`) and `Spherical`
(`normalizedHaar`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- Proposition VIII.3.1 (printed p. 323, PDF p. 89): for `f_1 ∈ °C(G)`, `f_2 ∈ C(G)` and
  `r ∈ ℝ` there is `c > 0` with
  `|∫_G f_1(a g a^{-1}) f_2(g) dg| ≤ c δ_0(a) (1 + σ(a))^{-r}` for `a ∈ Ā⁺_0 ∩ G^1`.
- Its proof (printed pp. 323–324, PDF pp. 89–90) fixes `α ∈ Δ_0`, the set
  `Ā⁺_0(α)`, compact open subgroups `Γ ⊆ U`, `Γ̄ ⊆ Ū`, and
  `S(a) = G - a^{-1} Γ a M Γ̄`. Lemma II.3.5 gives (2): there is `C_2 > 0` with
  `1 + σ(a) ≤ C_2 (1 + σ(g) + σ(a g a^{-1}))` for `a ∈ Ā⁺_0(α) ∩ G^1` and `g ∈ S(a)`.
  Then (3): there is `C_3 > 0` with
  `∫_{S(a)} |f_1(a g a^{-1}) f_2(g)| dg ≤ C_3 δ_0(a) (1 + σ(a))^{-r}`. Proof of (3): bound
  the integrand by `ν_{r'}(f_1) ν_{r'+r''}(f_2) Ξ(a g a^{-1}) Ξ(g)
  (1 + σ(a g a^{-1}))^{-r'} (1 + σ(g))^{-r'-r''}`; use (2) to extract `(1 + σ(a))^{-r'}`;
  extend the integral to `G`; replace `g` by `h g k` with `h, k ∈ K` and integrate over
  `h` and `k`, which by Lemmas II.1.3 and II.1.4 gives
  `∫_G Ξ(a g a^{-1}) Ξ(g) (1 + σ(g))^{-r''} dg = Ξ(a)^2 ∫_G Ξ(g)^2 (1 + σ(g))^{-r''} dg`;
  choose `r''` by Lemma II.1.5 and finish with the upper bound of Lemma II.1.1,
  `r' ≥ r + d`.
- The same averaging argument is used again at the end of the proof for `M`
  (printed p. 326, PDF p. 92: "Le même raisonnement que dans la preuve de (3)").

## Scope: abstract data and explicit hypotheses

The module works with a second-countable topological group `G` with its Borel
σ-algebra, an s-finite measure `μ` on `G` that is left and right invariant (for
Waldspurger's unimodular `G`, its Haar measure), a compact subgroup `K` and weights
`Ξ, σ : G → ℝ` satisfying `ConvolutionWeights μ K Ξ σ`. That structure (from
`Convolution`) records `Ξ > 0`, `σ ≥ 0`, continuity, the inequality
`1 + σ(g) ≤ (1 + σ(h)) (1 + σ(h^{-1} g))`, left `K`-invariance of `Ξ` and `σ`,
Lemma II.1.4 (`Ξ(g^{-1}) = Ξ(g)`), Lemma II.1.3 (`∫_K Ξ(g_1 k g_2) dk = Ξ(g_1) Ξ(g_2)` for
the Haar measure of `K` of mass one) and Lemma II.1.5 (`∫_G Ξ^2 (1 + σ)^{-d} < ∞` for some
natural `d`). For `Ξ = xi`, `SphericalTranslation.xi_convolutionWeights` proves all fields
except II.1.5 under its hypotheses. In addition, right `K`-invariance of `σ` is assumed.

The set `T` of the elements `a` and the sets `S(a)` are arbitrary. The inequality (2)
and the upper bound of Lemma II.1.1 on `T` are hypotheses. For Waldspurger's data,
`T = Ā⁺_0(α) ∩ G^1`, `S(a) = G - a^{-1} Γ a M Γ̄` and `e = δ_0^{1/2}`, so `e(a)^2 = δ_0(a)`;
none of these inputs is proved here.

## Definitions

- `ConjugationSigmaBound σ T S : Prop`, for `σ : G → ℝ`, `T ⊆ G` and sets `S(a) ⊆ G`:
  there is a real `C_2` with `1 + σ(a) ≤ C_2 (1 + σ(g) + σ(a g a^{-1}))` for all `a ∈ T`
  and `g ∈ S(a)`. With Waldspurger's `T` and `S(a)` this is inequality (2) of the proof
  of Proposition VIII.3.1, which he derives from Lemma II.3.5 and inequality (1)
  `1 + σ(a) ≤ C_1 (1 + ⟨α, H_0(a)⟩)` on `Ā⁺_0(α) ∩ G^1`. The constant is not required
  to be positive (the proof replaces it by `max(C_2, 1)`).

## Results

- `one_add_rpow_neg_mul_le`: for `x, y ≥ 0`, `t > 0`, `C > 0`, `r ≥ 0` with
  `t ≤ C (1 + x + y)`, `(1 + x)^{-r} (1 + y)^{-r} ≤ C^r t^{-r}`.
- `ConvolutionWeights.xi_mul_right`: `Ξ(g k) = Ξ(g)` for `k ∈ K`, from left invariance and
  Lemma II.1.4.
- `ConvolutionWeights.lintegral_xi_mul_left` (left-invariant `μ`): for measurable
  `W : G → ℝ≥0∞` with `W(k g) = W(g)` (`k ∈ K`),
  `∫⁻_G Ξ(x g y) W(g) dμ = Ξ(x) ∫⁻_G Ξ(g y) W(g) dμ`.
- `ConvolutionWeights.lintegral_xi_mul_right` (right-invariant `μ`): for measurable `W`
  with `W(g k) = W(g)`, `∫⁻_G Ξ(g y) W(g) dμ = Ξ(y) ∫⁻_G Ξ(g) W(g) dμ`.
- `ConvolutionWeights.lintegral_xi_mul_mul`: for measurable `W` bi-invariant under `K`,
  `∫⁻_G Ξ(x g y) W(g) dμ = Ξ(x) Ξ(y) ∫⁻_G Ξ(g) W(g) dμ`. With `x = a`, `y = a^{-1}` and
  Lemma II.1.4 this is the averaging identity of the proof of (3).
- `ConvolutionWeights.lintegral_conj_mul_le` (inequality (3)): assume `σ(g k) = σ(g)`
  for `k ∈ K`, `XiUpperBound Ξ σ T e` (there are `C`, `d` with
  `Ξ(a) ≤ C e(a) (1 + σ(a))^d` for `a ∈ T`), and `ConjugationSigmaBound σ T S`. Let
  `f_1, f_2 : G → ℂ` have `ν_r(f_i) < ∞` for every `r` (for instance `f_i ∈ C(G)`). Then
  for every real `r` there is `c ≥ 0` with
  `∫⁻_{S(a)} |f_1(a g a^{-1})| |f_2(g)| dμ(g) ≤ c e(a)^2 (1 + σ(a))^{-r}` for all `a ∈ T`.

Integrals are lower Lebesgue integrals of the absolute values, as in `Convolution`;
measurability of `S(a)` is not needed. The bound concerns `|f_1(a g a^{-1}) f_2(g)|`, as in
Waldspurger's (3).

## Proof notes

The proof follows Waldspurger's.

- Averaging. For `k ∈ K`, left invariance of `μ` and `W(k g) = W(g)` give
  `∫ Ξ(x g y) W(g) = ∫ Ξ(x k (g y)) W(g)`. Integrating over `k` against the probability
  measure `normalizedHaar K`, exchanging the integrals (Tonelli; the integrand is
  measurable on `K × G` since `G` is second countable) and applying Lemma II.1.3 to the
  inner integral gives the left formula; the right formula is the same with `g ↦ g k`
  and right invariance. The proof is that of `ConvolutionWeights.lintegral_xi_mul_xi`
  in `Convolution`.
- Inequality (3). Put `r'' = d_0` (the exponent of Lemma II.1.5 in `ConvolutionWeights`)
  and `r' = max(r + 2d, 0)`, and replace `C_2` by `max(C_2, 1)`. On `S(a)`,
  `|f_1(x)| ≤ ν_{r'}(f_1) Ξ(x) (1 + σ(x))^{-r'}` with `x = a g a^{-1}`, and
  `|f_2(g)| ≤ ν_{r'+r''}(f_2) Ξ(g) (1 + σ(g))^{-r'-r''}`; by (2) and
  `one_add_rpow_neg_mul_le`, `(1 + σ(g))^{-r'} (1 + σ(x))^{-r'} ≤ C_2^{r'} (1 + σ(a))^{-r'}`.
  Extend the integral to `G` and apply `lintegral_xi_mul_mul` with
  `W(g) = Ξ(g) (1 + σ(g))^{-r''}`, which is bi-invariant under `K`. With Lemma II.1.4 the
  result is `ν_{r'}(f_1) ν_{r'+r''}(f_2) C_2^{r'} (1 + σ(a))^{-r'} Ξ(a)^2 I` with
  `I = ∫ Ξ^2 (1 + σ)^{-r''} < ∞`. Finally `Ξ(a)^2 ≤ C^2 e(a)^2 (1 + σ(a))^{2d}` and
  `2d - r' ≤ -r`. Waldspurger writes `(1 + σ(a))^{-r'+d} δ_0(a)` at this point, with `d`
  the exponent for `Ξ(a)^2`; squaring the bound of Lemma II.1.1 gives the exponent `2d`
  used here.

## Open obligations

For Waldspurger's data this module proves neither inequality (2) (from Lemma II.3.5),
nor the upper bound of Lemma II.1.1, nor Lemma II.1.5, nor right `K`-invariance of `σ`
for his `σ` (it follows from the bi-invariance of `‖·‖` in I.1; `Height` proves it as
`height_mul_mul` for `K ≤ heightSubgroup τ`). The remaining part of Proposition
VIII.3.1, the integral `J(a)` over `a^{-1} Γ a M Γ̄` (which uses the cuspidality of `f_1`,
Proposition II.4.5, Lemmas II.3.1, II.3.3, II.3.4, II.4.1, II.4.4 and the integration
formula of I.1 on `U M Ū`), and Corollary VIII.3.2 are not formalized here.
