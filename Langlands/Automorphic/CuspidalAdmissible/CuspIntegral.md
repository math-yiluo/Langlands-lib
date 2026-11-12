# The square-integral cusp estimate

Module: `Langlands.Automorphic.CuspidalAdmissible.CuspIntegral`. Provenance: internal; the
square-integral form of the classical estimate for cusp forms along a maximal block parabolic,
obtained from the vanishing constant term and the pointwise estimate `exists_cusp_pointwise`.

## Generic measure lemmas (namespace `Langlands.Automorphic.CuspidalAdmissible`)

- `setLIntegral_mono_of_forall_mem`: for measurable `F ≤ H` on an arbitrary (possibly
  non-measurable) set `R`, `∫_R F ≤ ∫_R H` (the exceptional set `{F > H}` is measurable and
  disjoint from `R`).
- `setLIntegral_le_of_average`: if `φ g ≤ ∫ F(g, x) dμ(x)` for a probability measure `μ` and
  every slice satisfies `∫_R F(·, x) ≤ c`, then `∫_R φ ≤ c` (Tonelli,
  `lintegral_lintegral_swap`).
- `setLIntegral_translates_le`: for a left-invariant measure `ν`, continuous `φ_k` and a
  continuous curve `u` with `u(σ) R ⊆ t` for `σ ∈ [0, 1]`,
  `∫_R ∫_0^1 ∑_k |φ_k(u(σ) g)|² dσ dν(g) ≤ ∑_k ∫_t |φ_k|² dν` (Tonelli, left invariance
  `measurePreserving_mul_left` with `setLIntegral_comp_emb`, monotonicity in the set).

## Constant terms (namespace `Langlands.Global`)

- `continuous_constantTermIntegrand_uncurry`: `(X, g) ↦ constantTermIntegrand h G g X` is
  jointly continuous; it factors the continuous `(Y, g) ↦ G(u(Y) g)` through the open quotient
  map `matrixQuotientMap × id` (`constantTermIntegrand_mk`).
- `enorm_sq_le_lintegral_constantTerm`: if the constant term of `G` at `g` vanishes, then
  `|G(g)|² ≤ ∫ |G(g) - G(u(X) g)|² dX` over the Haar probability measure of the block quotient
  (write `G(g)` as the integral of `G(g) - G(u(X)g)`, then `‖∫ f‖ ≤ ∫ ‖f‖` and
  `sq_lintegral_le`).

## Main estimate

`exists_lintegral_cusp_le K n h L hL Q hQ`: there are a compact set `𝒲` of archimedean block
matrices and `B` (depending only on the block, `L` and `Q`) such that for every continuous
rational-left-invariant `G` with vanishing constant terms along the block, right invariant
under `L`, with smooth slices whose `lieDirection` derivatives are the slices of continuous
`dφ_k`, every left-invariant s-finite measure `ν`, every `ℓ ≥ 0`, every set `R` of points
`torInf x · q` (`q ∈ Q`, all across-the-block gaps of `x` at most `-ℓ`) and every set `t`
containing `u_∞(V) R` for `V ∈ 𝒲`:

`∫_R |G|² dν ≤ (e^{-ℓ} B)² ∑_k ∫_t |dφ_k|² dν`.

Proof: for each quotient variable `X`, the pointwise estimate (with `Y` a lift of `X`) bounds
`|G(g) - G(u(X) g)|²` on `R` by `(e^{-ℓ}B)² ∫_0^1 ∑_k |dφ_k(u_∞(σ W_∞) g)|² dσ`;
`setLIntegral_translates_le` bounds its integral over `R`. Jensen with the vanishing constant
term and `setLIntegral_le_of_average` (joint measurability from
`continuous_constantTermIntegrand_uncurry`) conclude.
