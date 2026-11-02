# Test functions in the Harish-Chandra Schwartz space

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TestFunctions`,
namespace `Langlands.HarishChandraSchwartz`. It builds on
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic` (the spaces `C_H` and
`C(G)` for arbitrary weights `Ξ`, `σ`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, section III.6 (printed
p. 271, PDF p. 37): "L'espace `C_c^∞(G)` est inclus et dense dans `C(G)`." Waldspurger
states this without proof.

## Scope: generic weights and explicit hypotheses

The weights `Ξ σ : G → ℝ` are arbitrary. Each result lists the properties of the
weights it uses as hypotheses:

- for the inclusion: `Ξ` continuous and positive, `σ` continuous and nonnegative;
- for the density, in addition: `σ` bi-invariant under some compact open subgroup
  `K₀`, and every sublevel set `{g | σ g ≤ N}` compact.

These are the properties one expects of Waldspurger's weights. `Ξ` is bi-invariant
under the maximal compact subgroup `K` (Lemma II.1.1) and is positive, being an
integral of a positive function over `K` (II.1). By I.1 (printed p. 242, PDF p. 8),
`σ = log ‖·‖` is nonnegative and bi-`K`-invariant. Waldspurger does not state that
the sublevel sets of `σ` are compact. That is expected to follow from the algebraic
embedding `τ : G → GL_n(F)` used to define `‖·‖`. This module does not prove any of
these facts or realize the source weights. That is left to the modules that
construct them.

The group `G` is a topological group that is Hausdorff, locally compact and totally
disconnected. These are the hypotheses of the Library statement
`Langlands.Hecke.TestFunction.CommonCompactOpenBiInvarianceStatement` (proved as
`Langlands.Hecke.TestFunction.commonCompactOpenBiInvariance`), which gives every test
function a compact open subgroup under which it is bi-invariant. The test functions
are the Library's `Langlands.HarmonicAnalysis.SchwartzBruhat G`: locally constant
compactly supported complex functions.

## Definitions

- `truncate σ N f`: the truncation `f · 1_{σ ≤ N}`, i.e. the indicator of the set
  `{g | σ g ≤ N}` applied to `f`.
- `ofSchwartzBruhat hΞc hΞ hσc hσ : SchwartzBruhat G →ₗ[ℂ] Space Ξ σ`: the inclusion
  `C_c^∞(G) → C(G)`. It does not change the underlying function
  (`coe_ofSchwartzBruhat`) and is injective (`ofSchwartzBruhat_injective`).
- `truncateSchwartzBruhat K₀ hσK hσN hf N`: for `f` bi-invariant under a compact open
  subgroup `K`, the truncation `f · 1_{σ ≤ N}` as a test function.

## Results

- `nu_lt_top_of_hasCompactSupport`: for continuous positive `Ξ` and continuous
  nonnegative `σ`, every continuous compactly supported `f` has `ν_r(f) < ∞` for all
  real `r`. Proof: `‖f‖ · Ξ⁻¹ (1 + σ)^r` is continuous with compact support, so it is
  bounded.
- `IsBiInvariant.isLocallyConstant`: a function bi-invariant under a compact open
  subgroup is locally constant.
- `exists_isBiInvariant_schwartzBruhat`: every test function is bi-invariant under a
  compact open subgroup contained in any given open subgroup (from
  `commonCompactOpenBiInvariance` applied to a single function).
- `schwartzBruhat_mem_levelSubmodule` and `schwartzBruhat_mem_schwartzSubmodule`:
  the inclusion `C_c^∞(G) ⊆ C(G)` of III.6, and more precisely, a test function
  bi-invariant under `K` lies in the level `C_K`.
- `IsBiInvariant.truncate`, `nu_truncate_le`: truncation along an `H`-bi-invariant
  `σ` preserves `H`-bi-invariance and does not increase any `ν_r`.
- `nu_sub_truncate_le`: for positive `Ξ` and `N ≥ 0`,
  `ν_r(f - f · 1_{σ ≤ N}) ≤ (1 + N)⁻¹ ν_{r+1}(f)`. On `{σ > N}` one has
  `(1 + σ)^r = (1 + σ)^{r+1} (1 + σ)⁻¹ ≤ (1 + N)⁻¹ (1 + σ)^{r+1}`.
- `denseRange_ofSchwartzBruhat`: the density of `C_c^∞(G)` in `C(G)` of III.6, under
  the hypotheses listed above.

## Proof of density

Let `F ∈ C(G)`. Since `K₀` exists, `F` lies in some level `C_K`, and hence in the
level `C_L` for `L = K ∩ K₀`. The truncations `F_n = F · 1_{σ ≤ n}`, `n ∈ ℕ`, are
bi-invariant under `L`. They are test functions: they are locally constant by
bi-invariance, and supported in the compact closed set `{σ ≤ n}`. They lie in `C_L`
because `ν_r(F_n) ≤ ν_r(F)`. By the tail estimate,
`ν_r(F_n - F) ≤ (1 + n)⁻¹ ν_{r+1}(F) → 0` for every `r`, so `F_n → F` in the
seminorm topology of `C_L`. The inclusion `C_L → C(G)` is continuous, so
`F_n → F` in `C(G)`. Each `F_n` is in the range of `ofSchwartzBruhat`.

The source gives no proof of the density. This truncation argument is the standard
one, and the Lean proof implements it.

## Not covered here

This module does not define a topology on `C_c^∞(G)`, and it does not state that the
inclusion is continuous for one. Translation invariance and the continuity of the
`G × G` action, Lemma III.6.1 (convolution) and the constant term are left to other
modules.
