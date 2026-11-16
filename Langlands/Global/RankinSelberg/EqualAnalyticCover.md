# Finiteness of integrals over `GL_n(F) \ GL_n(𝔸)` from bounds in Siegel coordinates

Module `Langlands.Global.RankinSelberg.EqualAnalyticCover`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

Fix a Siegel decomposition: a compact `Q₁` and `K` such that every `g` has a rational translate
`γ g = A(x) q` with `q ∈ Q₁` and `x` in the chamber `Chamber K` (the Library
`exists_siegelDecomposition`). Write `spread x = D(x) = Σ_i |x_i - x̄|` and `torusA x = A(x)`.

- **`finite_cover_of_siegel`**: there is a measurable `t ⊆ GL_n(𝔸)` meeting every
  `GL_n(F)`-orbit such that `∫_t w dν < ∞` for every left-invariant `ν` finite on compact sets
  and every `w ≥ 0` with
  `w(A(x) q) ≤ C e^(-D(x)) e^(-|Σ x|)` (`x ∈ Chamber (K + 2)`, `q ∈ Q₁`). The set `t` is the
  union of the translates `A(m) Q₂`, where `m` runs over the integer chamber vectors and
  `Q₂ = A([0,1]^n) Q₁`. Each translate contributes at most `|C| e^n e^(-Σ|m_i|)`
  (`shift_chamber`, `sum_abs_le_sum_abs_sub_mean`), which is summable
  (`summable_lattice_bound`, `lintegral_leftTranslateCover_lt_top`).
- **`lintegral_quotient_lt_top_of_siegel`**: a measurable `GL_n(F)`-invariant `w` on the adelic
  points satisfying the same bound has `∫_(GL_n(F)\GL_n(𝔸)) w < ∞`. The proof transfers through
  `LeftCosetSpace.lintegral_restrict_discreteQuotientMeasure_le`.
- `exponent_le_of_ge`, `exponent_le_of_le`: elementary bounds
  `A₀ |S| + α S ≤ -|S| + (|α| + A₀ + 1) b` on `S ≥ -b` when `α + A₀ ≤ -1`, and on `S ≤ b` when
  `α - A₀ ≥ 1`.

## Provenance

This adapts the weighted cover of the published `UnequalAnalyticDecay`
(`exists_weighted_cover_of_hasChamberDecay`) to integrands that decay in `|Σ x|`. The proof is
internal.
