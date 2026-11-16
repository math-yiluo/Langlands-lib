# Integrability on the regions `|det g| ≥ 1` and `|det g| < 1`

Module `Langlands.Global.RankinSelberg.EqualAnalyticRegions`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

`PointDecay Q₁ K P A₀` says that `|P(A(x) q)| ≤ C_c e^(-c D(x)) e^(A₀ |Σ x|)` on
`Chamber (K + 2) × Q₁`, for every `c ≥ 0` (with `C_c` depending on `c`) and a fixed `A₀ ≥ 0`.
This is the Library's chamber decay of cusp forms (`hasChamberDecay`), read on the adelic
points. With `L(g) = log |det g|` and `d = [F:ℚ]`:

- `regionGe P σ V = 1_(L ≥ 0) |P| e^(σ L) V` and `regionLt P σ V = 1_(L < 0) |P| e^(σ L) V`, both
  measurable and `GL_n(F)`-invariant for invariant `P` and `V`.
- **`lintegral_region_ge_lt_top`**: if `V(A(x) q) ≤ V₀ e^(N D(x)) e^(β Σ x)` with `N ≥ 0`, and
  `σ d + β + A₀ ≤ -1`, then `∫_(GL_n(F)\GL_n(𝔸)) regionGe P σ V < ∞`.
- **`lintegral_region_lt_lt_top`**: the same on `L < 0` when `σ d + β - A₀ ≥ 1`.

For `g = A(x) q` with `|log |det q|| ≤ ℓ₀` on `Q₁` (`log_detNorm_symm_torusA`):
`L(g) = d Σ x + log |det q|`. The region `L ≥ 0` forces `Σ x ≥ -ℓ₀/d`, and `L < 0` forces
`Σ x ≤ ℓ₀/d`. Taking `c = N + 1` in the decay of `P`, the product bound reduces to
`exponent_le_of_ge` / `exponent_le_of_le` (`region_real`). Then
`lintegral_quotient_lt_top_of_siegel` applies.

## Theta factors

- `thetaNorm_chamber_le`: for dominated `Ψ` and `N > n [F:ℚ]`,
  `Θ⁺(Ψ, A(x) q) ≤ V₀ e^(N D(x)) e^(-(N/n) Σ x)`. This is `exists_thetaNorm_le` with
  `t = x̄ - D(x) ≤ x_j` (`le_of_spread`).
- `thetaNorm_iota_chamber_le`: `Θ⁺(Ψ, ᵗ(A(x) q)⁻¹) ≤ V₀ e^(N D(x)) e^((N/n) Σ x)`, because
  `ᵗ(A(x) q)⁻¹ = A(-x) ᵗq⁻¹` (`inverseTranspose_torusA`) and `ᵗQ₁⁻¹` is compact.

## Provenance

These are the Siegel-domain estimates behind the absolute convergence statements in Cogdell
2004, §2.3, printed pp.209–210 (cusp forms are rapidly decreasing, theta series of moderate
growth). The proofs are internal. `enorm_mul_ofReal_le`, `measurable_log_detNorm`,
`torInf_zero'`, `torusA_neg_mul` and `detNorm_symm` are auxiliary.
