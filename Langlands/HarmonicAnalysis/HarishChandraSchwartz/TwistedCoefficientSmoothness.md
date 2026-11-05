# Smoothness of twisted coefficients: the core of Waldspurger's Proposition VII.1.3

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TwistedCoefficientSmoothness`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.TorusFourierSynthesis` (submitted with this module):
  `torusSynthesis`, `HasTorusMoments`, `torusPartialDerivList`,
  `isSmoothFiniteTorusFunction_torusSynthesis`, `torusSynthesis_add`,
  `torusSynthesis_const_mul`, `torusPartialDerivList_torusSynthesis` and
  `norm_torusPartialDerivList_torusSynthesis_le`;
- the published `HarishChandraSchwartz.Completeness` (`Space.nu_ne_top`) and, through
  `HarishChandraSchwartz.TemperedPairing`, the published `L2` and `Basic`: `nu`, `weight`,
  `Space Ξ σ` (Waldspurger's `𝒞(G)`), `Space.continuous`, `L2Weights` with
  `L2Weights.exponent`, `L2Weights.const`, `L2Weights.const_lt_top`, `L2Weights.nonneg`, and
  `L2Weights.lintegral_enorm_mul_le_of_nu`;
- the published `Langlands.Representation.Plancherel.SmoothTensorFamilies`:
  `Plancherel.smoothFiniteTorusFunctions J`, the subalgebra of smooth functions on
  `J → Circle`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082,
Proposition VII.1.3 and its proof, printed pp. 316–317 (PDF pp. 82–83).

Proposition VII.1.3: "Pour tout `f ∈ 𝒞(G)`, la fonction `ψ_f[𝒪, P]` appartient à
`C^∞(𝒪, P)`. L'application `𝒞(G) → C^∞(𝒪, P)`, `f ↦ ψ_f[𝒪, P]` est continue."

The proof reduces to `M = G` by Lemma VII.1.2, fixes `(ω, E) ∈ 𝒪` and a compact open subgroup
`H`, and sets, for `v ∈ E^H`, `v̌ ∈ Ě^H`, `f ∈ 𝒞_H`, `χ ∈ Im X(G)`,

> `C_{v⊗v̌,f}(χ) = d(ω ⊗ χ)⟨(ω ⊗ χ)(f̌)v, v̌⟩.`

It states: "L'énoncé résulte des assertions suivantes: pour tous `v ∈ E^M`, `v̌ ∈ Ě^M`, on a:
• pour tout `f ∈ 𝒞_H`, `C_{v⊗v̌,f} ∈ C^∞(Im X(G))`; • l'application
`𝒞_H → C^∞(Im X(G))`, `f ↦ C_{v⊗v̌,f}` est continue." (The page prints `E^M`, `Ě^M` here and
`E^H`, `Ě^H` in the lines before and after.) Then: "Notons que `d(ω ⊗ χ) = d(ω)` pour tout
`χ ∈ Im X(G)`. Les propriétés ci-dessus résultent de la majoration suivante. Soient `v ∈ E^H`,
`v̌ ∈ Ě^H`, `D` un opérateur différentiel à coefficients constants sur `Im X(G)`. Alors

> il existe `c > 0` et `r ∈ ℝ` tels que pour tous `f ∈ 𝒞_H`,
> `∫_G |f̌(g)⟨ω(g)v, v̌⟩D(χ(g))| dg ⩽ c ν_r(f)`.   (2)"

The proof of (2): there are `n ∈ ℕ` and `C₁ > 0` with `|D(χ(g))| ⩽ C₁(1 + |H_G(g)|)^n` for all
`χ ∈ Im X(G)`, `g ∈ G`; there is `C₂ > 0` with `|⟨ω(g)v, v̌⟩| ⩽ C₂ Ξ(g)` (Corollary III.1.2);
"La majoration (2) résulte alors du Lemme II.1.5."

## How the Lean statements model the source

- `G` is a topological group with a measure `μ`, and `Ξ, σ : G → ℝ` are abstract weights with
  `hw : L2Weights μ Ξ σ`: `Ξ > 0`, `σ ≥ 0`, and the conclusion of Lemma II.1.5,
  `∫_G Ξ(g)^2 (1 + σ(g))^{-d} dμ < ∞` for some `d` (`hw.exponent`, with value `hw.const`).
- The torus `Im X(G)` is modelled by `J → Circle` with `J` finite, and the character
  `χ ↦ χ(g)` by `z ↦ torusCharacter (n g) z = ∏_j z_j^{n(g)_j}` for a measurable
  `n : G → (J → ℤ)`. In the application `n(g)` would be the coordinates of the image of `g` in
  the lattice `G/G¹` in a basis; this identification is not made here.
- Waldspurger's bound for `D(χ(g))` comes from `|H_G(g)|`; it is modelled by the hypothesis
  `hnσ : ∀ g, ‖n g‖ ≤ C (1 + σ g)` (sup norm on `J → ℤ`), which combines the lattice
  coordinates with a bound of `|H_G(g)|` by a multiple of `1 + σ(g)`. Neither comparison is
  proved here.
- The coefficient `g ↦ ⟨ω(g)v, v̌⟩` is modelled by a continuous `φ : G → ℂ` with
  `hφ : ν_{-r}(φ) ≠ ∞`. Corollary III.1.2, `|⟨ω(g)v, v̌⟩| ⩽ C₂ Ξ(g)`, gives `ν_0(φ) ⩽ C₂`, i.e.
  the case `r = 0`.
- Waldspurger's `f̌` is the function `f` of the Lean statements. The Library's `nu_check`
  (`HarishChandraSchwartz.L2`) gives `ν_s(f̌) = ν_s(f)` when `Ξ(g⁻¹) = Ξ(g)` and
  `σ(g⁻¹) = σ(g)`; the passage from `f` to `f̌` is not made here.
- The constant `d(ω)` is omitted, and `⟨(ω ⊗ χ)(f̌)v, v̌⟩` is replaced by the integral
  `∫_G f̌(g) χ(g) ⟨ω(g)v, v̌⟩ dg` that defines it; no representation `ω` occurs.
- The operators `D` are the iterated angle derivatives `∂_l = ∂_{j₁} ∘ ⋯ ∘ ∂_{jₖ}`
  (`torusPartialDerivList`); every constant-coefficient operator on the torus is a linear
  combination of these, and the Lean statements are for the `∂_l` only.
- The results are for all `f ∈ 𝒞(G)` (`Space Ξ σ`), not only for one level `𝒞_H`.
- The Library has no topology on smooth functions on `J → Circle`. The continuity assertion is
  stated in seminorm form: for each `l`, `sup_z |∂_l C_f(z)| ≤ c' ν_s(f)` for all `f`. The
  seminorms `ν_s` define the topology of each `𝒞_H` (`Level.withSeminorms` in `Basic`), so this
  is the bound behind continuity of `𝒞_H → C^∞(J → Circle)` for the topology of uniform
  convergence of all `∂_l`; the topological statement itself is not made.

## Hypotheses of the results

- `nu_one_add_pow_smul`: `hσ : ∀ g, 0 ≤ σ g`.
- `L2Weights.lintegral_enorm_pow_mul_le`: `hw : L2Weights μ Ξ σ`, `Fintype J`,
  `hnσ : ∀ g, ‖n g‖ ≤ C * (1 + σ g)`, `hf : ν_{d+r+k}(f) ≠ ∞` and `hφ : ν_{-r}(φ) ≠ ∞`, where
  `d = hw.exponent`. No measurability is needed (lower Lebesgue integral).
- `L2Weights.hasTorusMoments_mul`, `L2Weights.integral_norm_pow_mul_le`: `G` a topological
  space with `OpensMeasurableSpace G`, `hw`, `hn : Measurable n`, `hnσ`, `hfc : Continuous f`,
  `hf : ∀ s, ν_s(f) ≠ ∞`, `hφc : Continuous φ`, `hφ : ν_{-r}(φ) ≠ ∞`.
- `Space.hasTorusMoments_mul`, `twistedCoefficientFamily`, `twistedCoefficientFamily_apply`:
  `G` a topological group with `OpensMeasurableSpace G` and `Nonempty (CompactOpenSubgroup G)`,
  `hw`, `hn`, `hnσ`, `hφc`, `hφ`.
- `torusPartialDerivList_twistedCoefficientFamily`,
  `norm_torusPartialDerivList_twistedCoefficientFamily_le`,
  `exists_norm_torusPartialDerivList_twistedCoefficientFamily_le`: the same, and
  `DecidableEq J`.

## Definitions

- `twistedCoefficientFamily hw hn hnσ hφc hφ : Space Ξ σ →ₗ[ℂ] Plancherel.smoothFiniteTorusFunctions J`
  sends `f ∈ 𝒞(G)` to the smooth function
  `z ↦ ∫_G f(g) φ(g) torusCharacter (n g) z dμ(g)`, which is `torusSynthesis μ n (f φ)`.
  This is the model of `χ ↦ ⟨(ω ⊗ χ)(f̌)v, v̌⟩` described above (without `d(ω)`).

## Results

- `nu_one_add_pow_smul`: `ν_s((1 + σ)^k f) = ν_{s+k}(f)`.
- `L2Weights.lintegral_enorm_pow_mul_le` (**estimate (2) in lattice coordinates**):
  `∫⁻ ‖n(g)‖^k |f(g)| |φ(g)| dμ ≤ |C|^k ν_{d+r+k}(f) ν_{-r}(φ) c`, with `c = hw.const`.
- `L2Weights.hasTorusMoments_mul`: `f φ` has finite moments of all orders along `n`.
- `L2Weights.integral_norm_pow_mul_le`: the real form,
  `∫ ‖n(g)‖^k |f(g) φ(g)| dμ ≤ |C|^k (ν_{d+r+k}(f) ν_{-r}(φ) c).toReal`.
- `Space.hasTorusMoments_mul`: the same moment property for `f ∈ 𝒞(G)`.
- `twistedCoefficientFamily_apply`: the value at `z` is
  `∫_G f(g) φ(g) torusCharacter (n g) z dμ(g)`.
- `torusPartialDerivList_twistedCoefficientFamily`: `∂_l` of the image of `f` is
  `z ↦ ∫_G (∏_{j ∈ l} i n(g)_j) f(g) φ(g) torusCharacter (n g) z dμ(g)`.
- `norm_torusPartialDerivList_twistedCoefficientFamily_le`: for all `z`,
  `|∂_l C_f(z)| ≤ |C|^{|l|} (ν_{d+r+|l|}(f) ν_{-r}(φ) c).toReal`, where `C_f` is the image of `f`.
- `exists_norm_torusPartialDerivList_twistedCoefficientFamily_le` (**continuity in seminorm
  form**): for each `l` there are `s` and `c'` with `|∂_l C_f(z)| ≤ c' ν_s(f).toReal` for all
  `f ∈ 𝒞(G)` and all `z`.

The smoothness assertion of the proof (first bullet) is the fact that
`twistedCoefficientFamily` takes values in `Plancherel.smoothFiniteTorusFunctions J`.

## Proof notes

1. `nu_one_add_pow_smul`: pointwise,
   `(1 + σ)^k · Ξ⁻¹ (1 + σ)^s = Ξ⁻¹ (1 + σ)^{s+k}` (`Real.rpow_add`, `Real.rpow_natCast`), and
   the suprema agree.
2. `L2Weights.lintegral_enorm_pow_mul_le`: `‖n(g)‖^k ≤ |C|^k (1 + σ(g))^k` by `hnσ`, so the
   integrand is at most `|C|^k |(1 + σ)^k f| |φ|`. The published
   `L2Weights.lintegral_enorm_mul_le_of_nu` for `(1 + σ)^k f` and `φ` gives
   `ν_{d+r}((1 + σ)^k f) ν_{-r}(φ) c`, and step 1 rewrites the first factor as
   `ν_{d+r+k}(f)`. This is Waldspurger's use of Lemma II.1.5.
3. `L2Weights.hasTorusMoments_mul`: `f φ` is continuous, hence a.e. strongly measurable, and
   `‖n‖` is measurable (`measurable_of_countable`); finiteness of each moment is step 2.
   `integral_norm_pow_mul_le` converts step 2 to a Bochner integral
   (`integral_eq_lintegral_of_nonneg_ae`, `ENNReal.toReal_mono`).
4. `twistedCoefficientFamily`: smoothness is `isSmoothFiniteTorusFunction_torusSynthesis`
   applied to step 3; additivity is `torusSynthesis_add`, homogeneity
   `torusSynthesis_const_mul`.
5. The derivative formula is `torusPartialDerivList_torusSynthesis`. The bound is
   `norm_torusPartialDerivList_torusSynthesis_le` followed by step 3 with `k = |l|`. The
   seminorm form takes `s = d + r + |l|` and `c' = |C|^{|l|} (ν_{-r}(φ) c).toReal`.

## Relation to the Library

`TemperedPairing` proves the case `k = 0` of the integrability and the continuity of
`f ↦ ∫ f φ` (III.7). `InducedCoefficientTwistXi` bounds families of induced coefficients by
`Ξ` (Lemma VI.2.2), the analogue of Corollary III.1.2 for the inducing data used in Section VI.
`FourierTransform` (Section VII.1) defines `f̂(ω) = d(ω) ω(f̌)` in the coefficient tensors and
proves Lemma VII.1.1; it has no dependence on a twisting character. A search of the Library for
`smoothFiniteTorusFunctions` found no family of coefficients of `𝒞(G)` parametrized by the
torus.

## Open obligations

- the identification of `Im X(G)` with `J → Circle`, of `χ(g)` with `torusCharacter (n g)`,
  and the bound `‖n(g)‖ ≤ C (1 + σ(g))` for Waldspurger's `Ξ`, `σ` and `H_G`;
- the passage from `f` to `f̌`, the factor `d(ω)`, and the identification of the model with
  `⟨(ω ⊗ χ)(f̌)v, v̌⟩` and with `ψ_f[𝒪, G]` through `FourierTransform`;
- a topology on smooth torus functions and the topological form of the continuity;
- the reduction from general `M` to `M = G` through Lemma VII.1.2.
