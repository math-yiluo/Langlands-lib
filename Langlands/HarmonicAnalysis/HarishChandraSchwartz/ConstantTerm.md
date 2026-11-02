# The constant term `f ↦ f^{(P)}` on the Harish-Chandra Schwartz space (III.6)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTerm`, namespace
`Langlands.HarishChandraSchwartz`. It builds on
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic` (seminorms `ν_r`, levels `C_H`,
`C(G)` with its inductive-limit topology, `Space.mkCLM`) and
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.Convolution` (`enorm_le_nu_mul`,
`weight_mul_ofReal`, `continuous_of_mem_levelSubmodule`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082.

- III.6 (printed p. 272, PDF p. 38): for a semi-standard parabolic subgroup `P = M U`,
  `f ∈ C(G)` and `m ∈ M`, `f^{(P)}(m) = δ_P(m)^{1/2} ∫_U f(m u) du`. "Il résulte de la
  Proposition II.4.5 appliquée à `P̄`" that the integral converges, that `f^{(P)}`
  belongs to `C(M)`, and that `C(G) → C(M)`, `f ↦ f^{(P)}`, is continuous.
  The same page then defines the `G × G`-equivariant map `f ↦ f^{(P),Ind}`.
- Proposition II.4.5 (printed p. 262, PDF p. 28): for every `d ∈ ℕ` there are `d' ∈ ℕ`
  and `c > 0` such that for all `m ∈ M`,
  `δ_P(m)^{-1/2} ∫_{Ū} Ξ(m ū) (1 + σ(m ū))^{-d'} dū ≤ c Ξ^M(m) (1 + σ(m))^{-d}`.
  A remark on p. 263 says it holds for semi-standard `P`. Applied to `P̄`, whose
  opposite unipotent radical is `U` and with `δ_{P̄}(m) = δ_P(m)^{-1}`, it gives the
  estimate `δ_P(m)^{1/2} ∫_U Ξ(m u) (1 + σ(m u))^{-d'} du ≤ c Ξ^M(m) (1 + σ(m))^{-d}`.

## Scope: abstract data and explicit hypotheses

The reductive group, `P = M U`, the Haar measure on `U`, `δ_P`, `Ξ^M` and `σ` are not
constructed here. The module works with:

- a topological group `G` with its Borel σ-algebra, weights `Ξ σ : G → ℝ`;
- subgroups `M` and `U` of `G`, a measure `ν` on `U` (Waldspurger's `du`), a character
  `δ : M →* ℝ≥0ˣ` (Waldspurger's `δ_P` on `M`), and weights `ΞM σM : M → ℝ` for `C(M)`
  (Waldspurger's `Ξ^M` and the restriction of `σ` to `M`). `M` carries the subspace
  topology.

Proposition II.4.5 is not proved here. Its conclusion, for `P̄`, is the hypothesis
`ConstantTermEstimate`. For Waldspurger's data it is an open proof obligation: the
source proves it from Lemmas II.4.4, II.3.1, II.1.1 (for `M`) and II.4.2 (printed
pp. 262–263). It is not an input that a consumer may assume.

The other hypotheses are collected in `ConstantTermData`:

- `isClosed`: `M` is closed (so `H ∩ M` is compact for compact `H`);
- `le_normalizer`: `M` normalizes `U` (`M ≤ Subgroup.normalizer U`);
- `delta_eq_one`: `δ(m) = 1` for `m ∈ M ∩ H`, for every compact open subgroup `H` of `G`;
- `map_conj`: for the same `m`, `ν` is invariant under `u ↦ m u m⁻¹`.

For Waldspurger's data these hold: `M` is closed and normalizes `U`; `δ_P` and the
modulus of the conjugation action of `M` on a Haar measure of `U` are continuous
characters of `M` with values in `ℝ_{>0}`, hence trivial on the compact subgroup
`M ∩ H`. These facts are not proved here and must be supplied when the data are
specialized.

The positivity hypotheses `Ξ > 0`, `σ ≥ 0`, `ΞM > 0`, `σM ≥ 0` appear on the results that
use them.

## Definitions

- `constantTerm ν δ f m = δ(m)^{1/2} ∫_U f(m u) dν(u)` for `f : G → ℂ` and `m ∈ M`
  (Bochner integral; its value is `0` where the integrand is not integrable, and the
  integrand is integrable for `f ∈ C(G)` by `integrable_of_mem_schwartzSubmodule`).
- `ConstantTermEstimate ν δ Ξ σ ΞM σM : Prop`: for every real `d` there are a real `d'`
  and `c ≥ 0` with
  `δ(m)^{1/2} ∫⁻_U Ξ(m u) (1 + σ(m u))^{-d'} dν(u) ≤ c Ξ^M(m) (1 + σ^M(m))^{-d}` for all
  `m ∈ M` (lower Lebesgue integral of the nonnegative function, in `ℝ≥0∞`). This is
  Proposition II.4.5 for `P̄`, with real instead of natural exponents.
- `conjUnipotent hMU m : U → U`, `u ↦ m u m⁻¹`, for `hMU : M ≤ Subgroup.normalizer U`.
- `CompactOpenSubgroup.subgroupOf hM H`: the compact open subgroup `H ∩ M` of `M` for a
  closed subgroup `M` (hypothesis `hM`) and a compact open subgroup `H` of `G`.
- `ConstantTermData ν δ : Prop`: the structure above.
- `Level.constantTerm hD h hΞ hσ hΞM hσM H : Level Ξ σ H →ₗ[ℂ] Level ΞM σM (H ∩ M)`:
  the constant term on levels.
- `Space.constantTermLinear` and `Space.constantTerm hD h hΞ hσ hΞM hσM :
  Space Ξ σ →L[ℂ] Space ΞM σM`: the constant term `C(G) → C(M)`, as a linear map and as
  a continuous linear map. `G` is assumed to have a compact open subgroup.

## Results

For a group `G` with a measurable structure, no further hypotheses:

- `constantTerm_smul`: `(c f)^{(P)} = c f^{(P)}`.
- `constantTerm_add`: `(f₁ + f₂)^{(P)} = f₁^{(P)} + f₂^{(P)}` when both integrands are
  integrable for every `m`.
- `enorm_constantTerm_le`: `|f^{(P)}(m)| ≤ δ(m)^{1/2} ∫_U |f(m u)| dν(u)`.

With `h : ConstantTermEstimate ν δ Ξ σ ΞM σM` and `Ξ > 0`, `σ ≥ 0`, `ΞM > 0`, `σM ≥ 0`:

- `ConstantTermEstimate.nu_le`: for every `d` there are `d'` and `c` with
  `ν^M_d(f^{(P)}) ≤ c ν_{d'}(f)` for every `f` with `ν_{d'}(f) < ∞`.

For a topological group `G` with its Borel σ-algebra (`ΞM`, `σM` only where stated):

- `continuous_conjUnipotent`: `u ↦ m u m⁻¹` is continuous on `U`.
- `CompactOpenSubgroup.mem_subgroupOf`: `m ∈ H ∩ M ↔ m ∈ H`.
- `ConstantTermEstimate.integrable` (`h`, `Ξ > 0`, `σ ≥ 0`): if `f` is continuous and
  `ν_r(f) < ∞` for all `r`, then `u ↦ f(m u)` is `ν`-integrable for every `m`
  (convergence assertion of III.6).
- `ConstantTermData.isBiInvariant` (`hD : ConstantTermData ν δ`): if `f` is continuous
  and bi-invariant under `H`, then `f^{(P)}` is bi-invariant under `H ∩ M`.
- `ConstantTermData.constantTerm_mem_levelSubmodule` (`hD`, `h`, positivity): for
  `f ∈ C_H`, `f^{(P)} ∈ C_{H ∩ M}`.
- `Level.coe_constantTerm`, `Level.continuous_constantTerm`: the level map is the
  constant term, and it is continuous.

If moreover `G` has a compact open subgroup:

- `ConstantTermEstimate.integrable_of_mem_schwartzSubmodule`: the integral defining
  `f^{(P)}(m)` converges absolutely for `f ∈ C(G)`.
- `ConstantTermData.constantTerm_mem_schwartzSubmodule`: `f^{(P)} ∈ C(M)` for
  `f ∈ C(G)`.
- `Space.coe_constantTerm`: `Space.constantTerm` is the constant term. Its continuity is
  part of the definition (`Space.mkCLM`): the map `C(G) → C(M)` is continuous (III.6).

The `G × G`-equivariant map `f ↦ f^{(P),Ind}` of III.6 and the transitivity diagram for
`P ⊆ P'` are not part of this module.

## Proof notes

1. `nu_le`. By `enorm_le_nu_mul`, `|f(m u)| ≤ ν_{d'}(f) Ξ(m u) (1 + σ(m u))^{-d'}`.
   Integrate over `U`, multiply by `δ(m)^{1/2}` and apply the estimate. This gives
   `|f^{(P)}(m)| ≤ c ν_{d'}(f) Ξ^M(m) (1 + σ^M(m))^{-d}`. Multiplying by the weight
   `Ξ^M(m)⁻¹ (1 + σ^M(m))^d` (`weight_mul_ofReal`) and taking the supremum over `m` gives
   the bound.
2. `integrable`. The integrand is continuous, hence measurable. The estimate with
   `d = 0` and `δ(m)^{1/2} ≠ 0` gives `∫⁻_U Ξ(m u) (1 + σ(m u))^{-d'} dν < ∞`, and the
   pointwise bound of step 1 gives finiteness of `∫⁻_U |f(m u)| dν`.
3. `isBiInvariant`. For `k₁, k₂ ∈ M ∩ H`, `k₁ m k₂ u = k₁ (m (k₂ u k₂⁻¹)) k₂`, so
   bi-invariance of `f` gives `f(k₁ m k₂ u) = f(m · k₂ u k₂⁻¹)`. Invariance of `ν` under
   conjugation by `k₂` (`integral_map`) and `δ(k₁) = δ(k₂) = 1` give
   `f^{(P)}(k₁ m k₂) = f^{(P)}(m)`.
4. Levels and continuity. Elements of `C_H` are continuous
   (`continuous_of_mem_levelSubmodule`), so steps 1–3 give `f^{(P)} ∈ C_{H ∩ M}`. The
   bound of step 1 bounds each seminorm of the image by a multiple of one seminorm of
   the argument, which gives continuity on levels
   (`WithSeminorms.continuous_of_isBounded`). Continuity on `C(G)` follows from the
   universal property III.6 (1) (`Space.mkCLM`), since the restriction to `C_H` is the
   level map followed by the inclusion `C_{H ∩ M} → C(M)`.
