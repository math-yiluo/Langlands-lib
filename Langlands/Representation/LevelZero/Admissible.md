# Admissibility of level-zero induction from a cuspidal representation

Lean module: `Langlands.Representation.LevelZero.Admissible`, namespace `Langlands.LevelZero`.

## Results

- `exists_pow_ball`: every neighbourhood of `0` in a nonarchimedean local field `F` contains
  all `x` with `v(x) ≤ v(ϖ)^M` for some `M`. A basic neighbourhood `{v x < γ}` has
  `γ = v(y) = v(ϖ)^e` for some `y` and `e`, and `M = (e + 1).toNat` works.
  `pow_le_pow_of_le` is the monotonicity of `M ↦ v(ϖ)^M`.
- `continuous_single`: `x ↦ Matrix.single i j x` is continuous.
- `exists_blockUnipotent_mem`: every open subgroup of `GL_n(F)` contains `blockUnipotent h X`
  for all `X` with `v(X i j) ≤ v(ϖ)^M`, for some `M`. Each `x ↦ blockUnipotent h (single i j x)`
  is continuous, so `exists_pow_ball` gives a bound for each entry; the maximum works because
  `blockUnipotent h` turns sums into products (`blockUnipotent_add`).
- `exists_cartan_monotone`: every `x ∈ GL_{m+1}(F)` is `k₁ diag(ϖ^μ) k₂` with `k₁, k₂` integral
  and `μ` monotone. This is the Library's Cartan decomposition (`Cartan.exists_cartan`, with an
  antitone exponent) applied to `x⁻¹`.
- `torus_eq_zpow_mul`: `diag(ϖ^μ) = (ϖ · 1)^c · diag(ϖ^(μ - c))`.
- `eval_eq_zero_of_gap` (**gap lemma**): let `σ` be cuspidal, `S` an open subgroup, `f` an
  `S`-fixed smooth induced function, `r ∈ GL_{m+1}(F)`, `0 < p < m + 1`, and `M` such that
  `r⁻¹ · blockUnipotent X · r ∈ S` whenever the `p × (m + 1 - p)` matrix `X` has entries of
  valuation at most `v(ϖ)^M`. If `μ j - μ i ≥ M` whenever `i < p ≤ j`, then
  `f(diag(ϖ^μ) r) = 0`.
- `le_mul_of_gaps_lt`: a monotone exponent with `μ 0 = 0` and all consecutive gaps below `M`
  satisfies `μ i ≤ i M`.
- `isCompact_maximalCompact`: `GL_{m+1}(𝒪_F)` is compact (`Conductor.isCompact_levelOpenSubgroup`
  at level `0`).
- `smoothInduced_isAdmissible`: for a finite-dimensional cuspidal representation `σ` of
  `GL_{m+1}(k)`, `IsAdmissible (smoothInduced J Λ)` with `J = inducingSubgroup m ϖ` and
  `Λ = inducingRep m hϖ σ`.

## Proofs

**Gap lemma.** Let `t = diag(ϖ^μ)` and `w = f(t r)`. For `γ` in the unipotent radical of the
two-block shape `(p, m + 1 - p)` over `k`, the entries of `γ` agree with those of `1` outside
the upper right block (`isBlockUnipotent_of_mem_cutShape`); so do those of its integral lift
`γ̂` and of `y = t⁻¹ γ̂ t`, whose upper right entries are `ϖ^(μ j - μ i) γ̂ i j` and have valuation
at most `v(ϖ)^M`. By `eq_blockUnipotent_of_pattern`, `y` is a block unipotent matrix, so
`r⁻¹ y r ∈ S`. Then `γ̂ (t r) = (t r)(r⁻¹ y r)` gives
`σ(γ) w = Λ(γ̂) f(t r) = f(γ̂ t r) = f(t r) = w`. Cuspidality of `σ`
(`cutShape_parabolic_ne_top`) forces `w = 0`.

**Admissibility.** Smoothness is `smoothInduced_smooth`. Let `S` be an open subgroup. By
compactness, `GL_{m+1}(𝒪_F)` is covered by finitely many translates `r S`, `r ∈ R`. Using
`exists_blockUnipotent_mem` for the open subgroups `r S r⁻¹` and finitely many cuts `p`, a single
`M` serves all `r ∈ R` and all `p` (`Filter.eventually_all_finset`, `Filter.eventually_all`).
Let `N = (m + 1) M`. The linear map from the `S`-fixed vectors to functions on the finite set
`(Fin (m + 1) → Fin (N + 1)) × R`, sending `f` to `(c, r) ↦ f(diag(ϖ^c) r)`, is injective, so
the fixed vectors are finite-dimensional (`Module.Finite.of_injective`). Indeed, write
`x = k₁ diag(ϖ^μ) k₂` with `μ` monotone, `c = μ 0`, `μ' = μ - c` and `k₂ = r s` with `r ∈ R`,
`s ∈ S`. Since `ϖ · 1` is central,
`x = ((ϖ · 1)^c k₁) (diag(ϖ^μ') r) s`, so `f(x) = Λ((ϖ · 1)^c k₁) f(diag(ϖ^μ') r)`. If some
consecutive gap of `μ'` is at least `M`, the gap lemma gives `f(diag(ϖ^μ') r) = 0`. Otherwise
`0 ≤ μ' i ≤ m M ≤ N` (`le_mul_of_gaps_lt`), so `f(diag(ϖ^μ') r)` is one of the coordinates of the
image, which vanishes.

Provenance: the admissibility of representations compactly induced from cuspidal types of level
zero (Bushnell–Kutzko 1993, `bushnell-kutzko-1993-admissible-dual`, SHA256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`, Theorem (6.2.2),
printed p. 203, where the compactly induced representation is irreducible and supercuspidal,
hence admissible). The proof here is the standard direct argument with the Cartan decomposition
and cuspidality, not the source's.
