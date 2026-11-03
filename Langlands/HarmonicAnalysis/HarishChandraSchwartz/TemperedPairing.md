# Functions of tempered growth and their pairing with `C(G)` (III.2, III.7)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedPairing`, namespace
`Langlands.HarishChandraSchwartz`. It imports the published module `L2` (`L2Weights`, its
exponent and constant, `L2Weights.lintegral_enorm_mul_le`) and, through it, `Basic`
(`nu`, `weight`, `nu_add_le`, `nu_mono`, `norm_le_of_nu`, `Level`, `Space`,
`Level.withSeminorms`, `Space.mkCLM`, `mem_schwartzSubmodule_iff`), `TestFunctions`
(`IsBiInvariant.isLocallyConstant`) and `Convolution` (`continuous_of_mem_levelSubmodule`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- III.2 (printed p. 265, PDF p. 31): `C^w_lisse(G)` is the space of `f ∈ C_lisse(G)` (functions
  bi-invariant under a compact open subgroup) for which there are `c > 0` and `r ∈ ℝ` with
  `|f(g)| ≤ c Ξ(g) (1 + σ(g))^r` for all `g`; `A^w(G) = A(G) ∩ C^w_lisse(G)`, and an
  admissible `π` is tempered if `A(π) ⊂ A^w(G)`.
- III.7 (printed p. 273, PDF p. 39), first sentences: "si `φ ∈ C^w_lisse(G)` et `f ∈ C(G)`,
  l'intégrale `∫_G f(g) φ(g) dg` est absolument convergente et l'application qui à `f`
  associe cette intégrale est continue. La preuve est identique à celle du Lemme III.6.1
  où l'on choisit `r ∈ ℝ` tel que `ν_r(φ)` soit fini." This is then applied to the
  coefficients `⟨π(g)v, v̌⟩` of a tempered `π` to define `π(f)` for `f ∈ C(G)`.

## Scope: abstract data and explicit hypotheses

`G` is a topological group (a measurable space with `OpensMeasurableSpace` for the
integrals), `Ξ, σ : G → ℝ` are arbitrary weights and `μ` is a measure on `G`. The
convergence uses the hypothesis `L2Weights μ Ξ σ` of `L2`: `Ξ > 0`, `σ ≥ 0` and
Lemma II.1.5, `∫_G Ξ^2 (1 + σ)^{-d} dμ < ∞` for some `d` (the exponent `hw.exponent`, with
value `hw.const`). For Waldspurger's `Ξ` and `σ` these are not proved here (Lemma II.1.5
is proved in `SquareIntegrability` from explicit Cartan bounds). The operator `π(f)` of
III.7, temperedness of representations and the coefficient spaces `A(π)` are not
defined here.

## Definitions

- `HasTemperedGrowth Ξ σ φ : Prop`: there are real `c` and `r` with
  `|φ(g)| ≤ c Ξ(g) (1 + σ(g))^r` for all `g` (the growth condition of III.2; `c` is not
  required to be positive).
- `IsTemperedSmooth Ξ σ φ : Prop`: `φ` is bi-invariant under some compact open subgroup
  and `HasTemperedGrowth Ξ σ φ`; that is, `φ ∈ C^w_lisse(G)`.
- `Level.temperedPairing hw hφc hφ K : Level Ξ σ K →ₗ[ℂ] ℂ` and
  `Space.temperedPairing hw hφc hφ : Space Ξ σ →L[ℂ] ℂ`: `f ↦ ∫_G f(g) φ(g) dμ(g)`, for
  `φ` continuous with `ν_{-r}(φ) < ∞`.

## Results

- `hasTemperedGrowth_iff`: for `Ξ > 0` and `σ ≥ 0`, `HasTemperedGrowth Ξ σ φ` holds if
  and only if `ν_s(φ) < ∞` for some `s` (with `s = -r`). This is the reformulation used
  in III.7 ("on choisit `r` tel que `ν_r(φ)` soit fini").
- `HasTemperedGrowth.add` (for `Ξ > 0`, `σ ≥ 0`) and `HasTemperedGrowth.smul`.
- `IsTemperedSmooth.continuous`: elements of `C^w_lisse(G)` are continuous (locally
  constant).
- `L2Weights.lintegral_enorm_mul_le_of_nu`: `∫_G |f| |φ| dμ ≤ ν_{d+r}(f) ν_{-r}(φ) c`, with
  `d`, `c` from `L2Weights`; `L2Weights.integrable_mul_of_nu` (integrability of `f φ` for
  continuous `f`, `φ` with these seminorms finite); `L2Weights.enorm_integral_mul_le`
  (`|∫ f φ dμ| ≤ ν_{d+r}(f) ν_{-r}(φ) c`).
- `Level.continuous_temperedPairing`: the functional is continuous on each level `C_K`,
  bounded by the seminorm `ν_{d+r}`.
- `Space.integrable_mul`: for `f ∈ C(G)`, `f φ` is integrable; `Space.temperedPairing`
  is a continuous linear functional on `C(G)` (by III.6 (1), `Space.mkCLM`);
  `Space.temperedPairing_apply`.

## Proof notes

As Waldspurger indicates, the estimate is that of Lemma III.6.1: with
`|f(g)| ≤ ν_{d+r}(f) Ξ(g) (1 + σ(g))^{-(d+r)}` and `|φ(g)| ≤ ν_{-r}(φ) Ξ(g) (1 + σ(g))^r`,
the product is bounded by `ν_{d+r}(f) ν_{-r}(φ) Ξ(g)^2 (1 + σ(g))^{-d}`, whose integral is
finite by Lemma II.1.5. The bound is `L2Weights.lintegral_enorm_mul_le` of `L2` with
`r₁ = d + r`, `r₂ = -r`. Continuity on `C(G)` follows from continuity on every level and
the universal property III.6 (1).

## Open obligations

The operator `π(f)` for a tempered admissible `π` and `f ∈ C(G)`, the identity
`π(f_1 * f_2) = π(f_1) π(f_2)`, finite rank and the continuity of `θ_π` (III.7), and the
statement that `f φ ∈ C(G)` for `f ∈ A(ω)`, `ω` square integrable and
`φ ∈ C_c(G/G^1)` (from Corollary III.1.2) are not formalized here.
