# The entire pieces of the continuation

Module `Langlands.Global.RankinSelberg.EqualAnalyticContinuation`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

## `EqualData`

The structure `EqualData F r` bundles the data the analysis needs:

- an idele class character `χ`;
- a continuous `GL_n(F)`-invariant `P` on `GL_n(𝔸)` (`n = r + 1`) with `P(a g) = χ(a) P(g)`;
- a standard additive character `ψ` and `Φ ∈ S(𝔸^n)`;
- a Siegel decomposition `(Q₁, K)`;
- a rate `A₀` with `PointDecay Q₁ K P A₀`.

In the application `P = φ φ'` for two cusp forms and `χ = ω ω'`.

## Definitions

With `L = Lg = log |det|`, `Φ̂ = Φh`, `Θ(g) = Θ(Φ, g)` and `Θι(g) = Θ(Φ̂, ᵗg⁻¹)`:

- the amplitudes `amp₁ = 1_(L ≥ 0) P Θ` and `amp₂ = 1_(L < 0) P Θι`;
- `A(s) = ∫ amp₁ e^(s L)` and `At(s) = Ã(s) = ∫ amp₂ e^(-s L)`, integrals over
  `GL_n(F) \ GL_n(𝔸)` (`μq`) evaluated at representatives;
- the theta factors `V₁ = Θ⁺(Φ, ·)` and `V₂ = Θ⁺(Φ̂, ι ·)`.

## Results

- Invariance and measurability of all these functions; `measurable_out` reads invariant
  measurable functions on the quotient.
- `lintegral_ge_V₁_lt_top σ`, `lintegral_lt_V₂_lt_top σ`: finite for every real `σ`. Choose
  `N` large in `thetaNorm_chamber_le` / `thetaNorm_iota_chamber_le` (`exists_nat_large`,
  `nat_div_bound`).
- `lintegral_lt_V₁_lt_top`, `lintegral_ge_V₂_lt_top`: finite for `σ` large, resp. small, with
  the fixed `N₀ = n [F:ℚ] + 1`.
- `lintegral_ge_one_lt_top`, `lintegral_lt_one_lt_top`: the residual regions.
- `integrable_amp₁`, `integrable_amp₂`: `|a_i| e^(σ L)` is integrable for every `σ`.
  Consequently `A` and `Ã` are entire (`differentiable_A`, `differentiable_At`), bounded on
  vertical strips (`bounded_A`, `bounded_At`), with integrable integrands
  (`integrable_A_integrand`, `integrable_At_integrand`). These use the published
  `UnequalAnalyticHolomorphy` lemmas.
- `integrable_resLt`, `integrable_resGe`: the residual integrands are integrable when
  `Re t · d - A₀ ≥ 1`, resp. `Re t · d + A₀ ≤ -1`.

## Provenance

This is the classical splitting of the integral at `|det g| = 1`, with an entire part on each
side (Cogdell 2004, §2.3, printed p.209, for the Eisenstein series;
Jacquet–Piatetski-Shapiro–Shalika). The proofs are internal; `EqualData` and the names above
are internal encodings.
