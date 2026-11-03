# The cuspidal part of Proposition VIII.3.1

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalDecay`, namespace
`Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConjugationBound` (the `K × K`-averaging
identity `ConvolutionWeights.lintegral_xi_mul_mul`, `ConvolutionWeights.xi_mul_right` and
inequality (3)) and, through it, `SphericalBounds` (`XiUpperBound`), `ConstantTermBound`
(`IsDoubleCosetCover`, `XiLowerBound`, `UnipotentXiBound`, `SigmaProductBound`,
`UnipotentWeightIntegrable`, `IsConjModulus.lintegral_comp`, `one_add_rpow_neg_le`),
`ConstantTermInd` (`IsConjModulus`, `IsConjModulus.integral_comp`,
`conjUnipotentHomeomorph`), `ConstantTerm` (`ConstantTermEstimate`, `conjUnipotent`,
`continuous_conjUnipotent`) and `Convolution` (`ConvolutionWeights`, `enorm_le_nu_mul`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

Proposition VIII.3.1 (printed p. 323, PDF p. 89): for `f_1 ∈ °C(G)`, `f_2 ∈ C(G)` and
`r ∈ ℝ` there is `c > 0` with `|∫_G f_1(a g a^{-1}) f_2(g) dg| ≤ c δ_0(a) (1 + σ(a))^{-r}`
for all `a ∈ Ā⁺_0 ∩ G^1`. The proof (printed pp. 323–326, PDF pp. 89–92) fixes
`α ∈ Δ_0`, the maximal standard `P = M U` with `Δ^M_0 = Δ_0 - {α}`, compact open
subgroups `Γ ⊆ U` and `Γ̄ ⊆ Ū` such that `f_1` is left `Γ`-invariant and `f_2` is right
`Γ̄`-invariant, and `S(a) = G - a^{-1} Γ a M Γ̄`. Inequality (3) bounds the integral over
`S(a)` (module `ConjugationBound`). For the rest, printed pp. 324–326:

- `J(a) = ∫_{a^{-1} Γ a M Γ̄} f_1(a g a^{-1}) f_2(g) dg
  = γ(G|M)^{-1} ∫_{a^{-1}Γa × M × Γ̄} f_1(a u m ū a^{-1}) f_2(u m ū) δ_P(m)^{-1} dū dm du`,
  and with `φ_1(a, m) = δ_P(m)^{-1/2} ∫_{Γ̄} f_1(m a ū a^{-1}) dū` and
  `φ_2(a, m) = δ_P(m)^{-1/2} ∫_{a^{-1} Γ a} f_2(u m) du`,
  `J(a) = γ(G|M)^{-1} ∫_M φ_1(a, a m a^{-1}) φ_2(a, m) dm`.
- (4): for every `d` there is `C_6` with `|φ_2(a, m)| ≤ C_6 Ξ^M(m) (1 + σ(m))^{-d}` for all
  `a` and `m`, from Proposition II.4.5 for `P̄`.
- `φ_1(a, m) = δ_P(a) δ_P(m)^{-1/2} ∫_{a Γ̄ a^{-1}} f_1(m ū) dū`. Since `f_1` is cuspidal,
  `f_1^{(P̄)} = 0` ("Lemme VII.2.1" in the text; the cuspidality lemma is VIII.2.1, as
  recorded in the public source map), so `∫_Ū f_1(m ū) dū = 0` and the integral over
  `a Γ̄ a^{-1}` is minus the integral over its complement. With
  `Ū_a(δ) = {ū ∈ Ū ; δ (1 + σ(a)) ≤ 1 + σ(ū)}`, inequality (2) and Lemma II.3.3 give
  `Ū - a Γ̄ a^{-1} ⊂ Ū_a(δ)` for some `δ > 0`; hence (5):
  `|φ_1(a, m)| ≤ δ_P(a) δ_P(m)^{-1/2} ∫_{Ū_a} |f_1(m ū)| dū`.
- (6): for every `d'` there are `r'` and `C_9` with
  `δ_P(m)^{-1/2} ∫_{Ū_a} Ξ(m ū) (1 + σ(m ū))^{-r'} dū ≤ C_9 (1 + σ(a))^{-d'} Ξ^M(m)`.
  The proof reduces to `m ∈ M̄^{M+}_0` (`Ū_a` is invariant under conjugation by
  `K ∩ M`), uses Lemmas II.3.1, II.4.4 and II.1.1, and bounds the integral over `Ū_a` by a
  sum over the level sets `Ū(n)`, `n ≥ ε σ(a)`, with Lemmas II.3.4 (for `P_0`) and II.4.1.
- From (4), (5), (6): `|J(a)| ≤ C_14 δ_P(a) (1 + σ(a))^{-d'}
  ∫_M Ξ^M(m) Ξ^M(a m a^{-1}) (1 + σ(m))^{-d} dm`, and "le même raisonnement que dans la
  preuve de (3)" gives `|J(a)| ≤ C_14 δ_P(a) Ξ^M(a)^2 (1 + σ(a))^{-d'}
  ∫_M Ξ^M(m)^2 (1 + σ(m))^{-d} dm`; Lemmas II.1.1 and II.1.5 for `M` give
  `|J(a)| ≤ C_15 δ_0(a) (1 + σ(a))^{-r}`. With (3) this proves the proposition on
  `Ā⁺_0(α) ∩ G^1`.

## Scope: abstract data and explicit hypotheses

The reductive group, `P = M U`, `Ū`, `K`, `Γ`, `Γ̄`, the Haar measures and the modulus
characters are not constructed. The module works with a topological group `G` with its
Borel σ-algebra and subgroups `M`, `U`, `U'` of `G` normalized by `M` (proofs `hMU`,
`hMU'`), where:

- `U` plays `Ū`, with a measure `ν` (`dū`) and a character `δ : M →* ℝ≥0ˣ` playing
  `δ_{P̄} = δ_P^{-1}`, so `δ(m)^{1/2} = δ_P(m)^{-1/2}` and `δ(a)^{-1} = δ_P(a)`;
- `U'` plays `U`, with a measure `ν'` (`du`) and a character `δ'` playing `δ_P`;
- `Ξ, σ : G → ℝ`, `Ξ^M : M → ℝ`, and the height on `M` is the restriction of `σ`;
- `K_M` is a compact subgroup of `M` (Waldspurger's `K ∩ M`) and `μ_M` is a left and right
  invariant s-finite measure on the second-countable group `M` (its Haar measure).

The identification of `δ` and `δ'` with `δ_P^{-1}` and `δ_P` is not made; the relation
`δ_P(a) δ^M_0(a) = δ_0(a)` enters only through the hypothesis `heA` below. The
decomposition of `∫_G` into the integral over `S(a)` and `J(a)` and the formula for `J(a)`
(the integration formula I.1 (2) on `U M Ū` and the invariance properties of `f_1`, `f_2`)
are a hypothesis of `conjugationIntegralBound_of_split`; they are not proved here.

## Definitions

- `cuspidalFactor hMU ν δ Γ f₁ a m = δ(m)^{1/2} ∫_U 1_Γ(u) f₁(m a u a^{-1}) dν(u)`, for
  `a, m ∈ M` and `Γ ⊆ U`: Waldspurger's `φ_1(a, m)` (with `Γ = Γ̄`).
- `unipotentFactor ν' δ' A f₂ m = δ'(m)^{-1/2} ∫_A f₂(u m) dν'(u)` for `A ⊆ U'`:
  Waldspurger's `φ_2(a, m)` with `A = a^{-1} Γ a`.
- `ConjugationIntegralBound μ T f₁ f₂ e σ : Prop`, for `T ⊆ M`: for every real `r` there
  is `c ≥ 0` with `|∫_G f₁(a g a^{-1}) f₂(g) dμ(g)| ≤ c e(a)^2 (1 + σ(a))^{-r}` for all
  `a ∈ T`. With `e = δ_0^{1/2}` this is the conclusion of Proposition VIII.3.1 on `T`.

## Results

- `setLIntegral_estimate_of_bounds` (inequality (6)): under the hypotheses of
  `constantTermEstimate_of_bounds` in `ConstantTermBound` for `(M, U, ν, δ)`, namely
  `IsConjModulus hMU ν δ`; `δ(k) = 1` for `k ∈ K_M`; `IsDoubleCosetCover K_M S`;
  `Ξ(k₁ g k₂) = Ξ(g)` and `σ(k₁ g k₂) = σ(g)` for `k₁, k₂ ∈ K_M`; `Ξ^M(k₁ m k₂) = Ξ^M(m)`;
  `σ ≥ 0`, `Ξ^M ≥ 0`, `e ≥ 0` on `S`, `w ≥ 0`; `e(m) δ(m)^{1/2} ≤ e^M(m)` on `S`;
  `UnipotentXiBound Ξ σ S e w` (II.4.4), `SigmaProductBound M U σ` (II.3.1),
  `XiLowerBound Ξ^M S e^M` (II.1.1 for `M`) and `UnipotentWeightIntegrable ν w σ`
  (II.4.2); for every `d` and every `d'' ≥ 0` there are `d'`
  and `c` such that for every `V ⊆ U` and `t > 0` with `t ≤ 1 + σ` on `V` and `V`
  invariant under conjugation by `K_M`, and every `m ∈ M`,
  `δ(m)^{1/2} ∫⁻_U 1_V(u) Ξ(m u) (1 + σ(m u))^{-d'} dν(u) ≤ c t^{-d''} Ξ^M(m) (1 + σ(m))^{-d}`.
  The constants do not depend on `V` and `t`.
- `enorm_nnreal_mul`: `|s z| = s |z|` for `s ≥ 0` real and `z ∈ ℂ`.
- `enorm_setIntegral_le_of_integral_eq_zero`: if `f` is integrable with `∫ f = 0`, `B` is
  measurable and `Bᶜ ⊆ V`, then `|∫_B f| ≤ ∫⁻ 1_V |f|`.
- `IsConjModulus.lintegral_mul_right`: under `IsConjModulus hMU ν δ`,
  `∫⁻_U φ(u m) dν(u) = δ(m) ∫⁻_U φ(m u) dν(u)`.
- `ConstantTermEstimate.lintegral_mul_right_le` (inequality (4)): from
  `IsConjModulus hMU ν δ` and `ConstantTermEstimate ν δ Ξ σ ΞM σM` (Proposition II.4.5,
  here for `(M, U')` in the application), for every `d` there are `d'` and `c` with
  `δ(m)^{-1/2} ∫⁻_U |f(u m)| dν(u) ≤ c ν_{d'}(f) Ξ^M(m) (1 + σ^M(m))^{-d}` whenever
  `ν_{d'}(f) < ∞`.
- `IsConjModulus.enorm_integral_conj_le` (inequality (5)): if `∫_U f(m v) dν(v) = 0`,
  `v ↦ f(m v)` is integrable, `Γ ⊆ U` is measurable and the complement of
  `a Γ a^{-1}` (written as the preimage of `Γ` under `v ↦ a^{-1} v a`) lies in `V`, then
  `|∫_U 1_Γ(u) f(m a u a^{-1}) dν(u)| ≤ δ(a)^{-1} ∫⁻_U 1_V(v) |f(m v)| dν(v)`.
- `lintegral_cuspidal_le` (the estimate of `J(a)`): assume the hypotheses of
  `setLIntegral_estimate_of_bounds` for `(M, U, ν, δ)` (except bi-invariance and
  nonnegativity of `Ξ^M`, which follow from `ConvolutionWeights` for `M`), `Ξ > 0`;
  `IsConjModulus hMU' ν' δ'` and `ConstantTermEstimate ν' δ' Ξ σ ΞM σ|_M`;
  `ConvolutionWeights μ_M K_M Ξ^M σ|_M` (continuity, Lemmas II.1.3, II.1.4, II.1.5 for `M`);
  `XiUpperBound Ξ^M σ|_M T e_A` (the upper bound of Lemma II.1.1 for `M` on `T`) and
  `heA : δ(a)^{-1} e_A(a)^2 ≤ e_0(a)^2` on `T`; a measurable `Γ ⊆ U`, sets `A(a) ⊆ U'`,
  `V(a) ⊆ U` and numbers `t(a)` with `t(a) ≤ 1 + σ` on `V(a)`, `V(a)` invariant under
  conjugation by `K_M`, the complement of `a Γ a^{-1}` contained in `V(a)`, and
  `δ_1 (1 + σ(a)) ≤ t(a)` for some `δ_1 > 0`; `f₁`, `f₂` with all `ν_r` finite,
  `v ↦ f₁(m v)` integrable on `U` and `∫_U f₁(m v) dν(v) = 0` for every `m ∈ M`
  (cuspidality along `P̄`). Then for every `r` there is `c` with
  `∫⁻_M |φ_1(a, a m a^{-1})| |φ_2(a, m)| dμ_M(m) ≤ c e_0(a)^2 (1 + σ(a))^{-r}` for all
  `a ∈ T`, where `φ_1 = cuspidalFactor hMU ν δ Γ f₁` and
  `φ_2(a, ·) = unipotentFactor ν' δ' (A(a)) f₂`.
- `enorm_integral_conj_le_of_split` and `conjugationIntegralBound_of_split`
  (Proposition VIII.3.1 on `T`): if
  `∫_G f₁(a g a^{-1}) f₂(g) dμ = ∫_{S(a)} f₁(a g a^{-1}) f₂(g) dμ + γ ∫_M φ_1(a, m) φ_2(a, m) dμ_M`
  for `a ∈ T` (for Waldspurger's data, `γ = γ(G|M)^{-1}` and
  `φ_1(a, m) = cuspidalFactor … a (a m a^{-1})`), and the two pieces satisfy bounds
  `c e(a)^2 (1 + σ(a))^{-r}` for every `r` (inequality (3), `lintegral_conj_mul_le`, and
  `lintegral_cuspidal_le`), then `ConjugationIntegralBound μ T f₁ f₂ e σ`.

For Waldspurger's data, `e_0 = δ_0^{1/2}`, `e_A = (δ^M_0)^{1/2}`, `t(a) = δ (1 + σ(a))`,
`V(a) = Ū_a(δ)`, `T = Ā⁺_0(α) ∩ G^1`, and `heA` is the identity
`δ_P(a) δ^M_0(a) = δ_0(a)`. `lintegral_conj_mul_le` is stated for `T ⊆ G` and
`e : G → ℝ`; it applies to the image of `T ⊆ M` in `G`.

## Proof notes

- (6). The proof is that of `constantTermEstimate_of_bounds` with the integrand multiplied
  by `1_V`: with `r = max(d, d_2 + d'', 0)` and `d' = D + 2r`, the integrand at
  `s ∈ S` is at most `A(s) w(u) (1 + σ(u))^{-r}`, and on `V`,
  `(1 + σ(u))^{-r} ≤ (1 + σ(u))^{-d''} (1 + σ(u))^{-d_2} ≤ t^{-d''} (1 + σ(u))^{-d_2}`; the
  remaining integral is finite by Lemma II.4.2. The reduction from `m = k_1 s k_2` to `s`
  uses the conjugation invariance of `V`. This differs from Waldspurger's proof of (6),
  which bounds the integral over `Ū_a` through the level sets `Ū(n)` with Lemmas II.3.4
  and II.4.1; here those lemmas enter only through Lemma II.4.2 (see `SphericalBounds`).
- (4). `u m = m (m^{-1} u m)`; the change of variables `u ↦ m^{-1} u m`
  (`IsConjModulus.lintegral_comp`) gives the factor `δ(m)`, and
  `δ(m)^{-1/2} δ(m) = δ(m)^{1/2}`; then `|f| ≤ ν_{d'}(f) Ξ (1 + σ)^{-d'}` and
  `ConstantTermEstimate`. The restriction to `a^{-1} Γ a` is dropped.
- (5). `1_Γ(u) = 1_B(a u a^{-1})` for `B` the preimage of `Γ` under `v ↦ a^{-1} v a`; the
  change of variables (`IsConjModulus.integral_comp`) gives `δ(a)^{-1} ∫_B f(m v) dν(v)`,
  and cuspidality with `enorm_setIntegral_le_of_integral_eq_zero` gives the bound.
- `J(a)`. For `m' = a m a^{-1}`, (5) and (6) (with `d = 0` and
  `d'' = max(r + 2D, 0)`, `D` the exponent of the upper bound of Lemma II.1.1 for `M`)
  give `|φ_1(a, m')| ≤ δ(a)^{-1} ν(f₁) c_6 t(a)^{-d''} Ξ^M(a m a^{-1})`; (4) with
  `d = d_0` (the exponent of Lemma II.1.5 for `M`) gives
  `|φ_2(a, m)| ≤ c_4 ν(f₂) Ξ^M(m) (1 + σ(m))^{-d_0}`. The averaging identity of
  `ConjugationBound` on `M` with `W(m) = Ξ^M(m) (1 + σ(m))^{-d_0}` and Lemma II.1.4 for
  `M` give `Ξ^M(a)^2 ∫_M Ξ^M(m)^2 (1 + σ(m))^{-d_0} dm`. Finally
  `t(a)^{-d''} ≤ δ_1^{-d''} (1 + σ(a))^{-d''}`,
  `Ξ^M(a)^2 ≤ C^2 e_A(a)^2 (1 + σ(a))^{2D}`, `heA`, and `2D - d'' ≤ -r`. Right
  `K_M`-invariance of `σ` on `M` follows from the bi-invariance hypothesis on `σ`.

## Open obligations

For Waldspurger's data none of the following is proved here: the decomposition
`∫_G = ∫_{S(a)} + J(a)` and the formula `J(a) = γ(G|M)^{-1} ∫_M φ_1(a, a m a^{-1}) φ_2(a, m) dm`
(integration formula I.1 (2) on `U M Ū`, invariance of `f_1` and `f_2` under `Γ` and `Γ̄`);
the inclusion `Ū - a Γ̄ a^{-1} ⊂ Ū_a(δ)` (from inequality (2) and Lemma II.3.3); the
cuspidality `f_1^{(P̄)} = 0` for `f_1 ∈ °C(G)` (Lemma VIII.2.1); the ingredients of
Proposition II.4.5 and of `ConvolutionWeights` for `G` and `M`; the identity
`δ_P(a) δ^M_0(a) = δ_0(a)`; the reduction of Proposition VIII.3.1 to the sets
`Ā⁺_0(α) ∩ G^1` for `α ∈ Δ_0` and the case `G = M_0`; and Corollary VIII.3.2.
