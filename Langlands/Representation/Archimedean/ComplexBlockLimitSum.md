# The limit argument along `P_{a,k+1}` for finite sums of matrix coefficients

Lean module: `Langlands.Representation.Archimedean.ComplexBlockLimitSum`.

Worker 728 wrote this module for Task 7064 (`e4a22cc7-0a28-44a3-afc6-38bb7c243851`). It is a
helper for the proof of `ComplexReverseIntertwinerKernelStatement` at tied exponents (Worker 5677's
route). That proof compares two matrix-coefficient integrals and needs an identity between their
leading terms, not only the vanishing statement of `ComplexBlockLimit`.

Notation as in `ComplexBlockLimit`: `GL_N(ℂ)` is `Langlands.GeneralLinear N ℂ` and `U(N)` is
`unitaryCompact ℂ N`, with the Haar probability measure `ComplexDuality.unitaryHaar N`.
`n̄(X) = [[1, 0], [X, 1]]` is `blockLowerGL` and `diag(κ₁, κ₂)` is `blockDiagGL`. `IsPhasePower χ e`
and `dualChar χ` (`l, z ↦ (χ_l z)⁻¹`) come from `ComplexPartialJacquet`. `Φ u h s κ₁ κ₂ X` is the
integrand `u(n̄(s⁻¹X) diag(κ₁, κ₂)) h(n̄(X) diag(κ₁, κ₂))` of `ComplexBlockLimit`. Unprefixed names
below are in the namespace `Langlands.Archimedean.ComplexBlockLimitSum`.

## Definitions

* `tripleΦ u h s = ∫_{U(a)} ∫_{U(k+1)} ∫_{M_{(k+1)×a}(ℂ)} Φ u h s κ₁ κ₂ X dX dκ₂ dκ₁`.
* `blockTerm u h = ∫_{U(a)} ∫_{U(k+1)} u(diag(κ₁, κ₂)) (∫_X h(n̄(X) diag(κ₁, κ₂)) dX) dκ₂ dκ₁`,
  the leading term. `ComplexBlockLimit` shows that it vanishes when `u` and `h` have zero matrix
  coefficient integrals.

## Results

All results assume the order hypotheses of `ComplexBlockLimit`. These are: `IsPhasePower χ e`;
`Re e_{l+1} ≤ Re e_l` for `l < a`; `Re e_a < Re e_{a−1}` when `a ≥ 1`; and
`Re e_a = ⋯ = Re e_{a+k}`. The results also take the statements
`ComplexBlockChartIntegrableStatement` (`hT1`) and `ComplexBlockParabolicIntegrationStatement`
(`hT3`) as hypotheses. The Library proves both in
`ComplexBlockChartIntegralProof` and `ComplexBlockParabolicIntegrationProof`;
`ComplexReverseIntertwinerTied` supplies those proofs to the final reduction.

* `sum_tripleΦ_eq_zero` (needs `hT3` only). Let `S` be a finite set of indices, `u_i` in the
  principal series of `χ⁻¹` and `h_i` in that of `χ` for `i ∈ S`. Suppose
  `∑_{i∈S} ∫_{U(a+k+1)} u_i(κ d(s)) h_i(κ) dκ = 0` for every `s ∈ ℂˣ`, where
  `d(s) = diag(1_a, s·1_{k+1})` is `ComplexBlockLimit.dTail s` (the "ray hypothesis"). Then
  `∑_{i∈S} tripleΦ u_i h_i s = 0` for every real `s > 0`.
* `tendsto_tripleΦ` (needs `hT1` only). For a single pair, `tripleΦ u h (n+1) → blockTerm u h` as
  `n → ∞`. No vanishing hypothesis is needed.
* `sum_blockTerm_eq_zero`. Under the hypothesis of `sum_tripleΦ_eq_zero`,
  `∑_{i∈S} blockTerm u_i h_i = 0`.
* `blockTerm_eq_of_integral_eq` (identity form). Suppose `u₁, u₂` lie in the principal series of
  `χ⁻¹`, `h₁, h₂` lie in that of `χ`, and
  `∫_U u₁(κ d(s)) h₁(κ) dκ = ∫_U u₂(κ d(s)) h₂(κ) dκ` for every `s ∈ ℂˣ`. Then
  `blockTerm u₁ h₁ = blockTerm u₂ h₂`.

The hypotheses are needed only along the ray `d(s)`, not for every `g ∈ GL_{a+k+1}(ℂ)`; a
hypothesis for every `g` implies them. `ComplexBlockLimit` states its hypothesis for every `g`,
but its proof uses it only at `g = d(s)`.

Provenance. Derived (internal). This is the leading-term argument of the published module
`ComplexBlockLimit` (Worker 140, Task 7063), made linear in the pair `(u, h)` and with the
hypothesis restricted to the ray `d(s)`. It makes no claim beyond the Lean statements.

## Proof

* `sum_tripleΦ_eq_zero` follows the proof of `ComplexBlockLimit.integral_Φ_eq_zero`. Put
  `s' = s` as a unit, `d = dTail s' = diag(1_a, s·1_{k+1})` and
  `c' = principalSeriesCharacter (dualChar χ) (tailEntries s')`. For each `i ∈ S` the function
  `F_i(y) = u_i(y d) h_i(y)` lies in the principal series of the modulus character, by
  `rightTranslation_mem_principalSeries`, `contMDiff_mul_fun` and
  `principalSeriesCharacter_dual_mul`. Write `c > 0` for the constant of `hT3` (at `a`, `k+1`).
  Then `hT3` gives `∫_U F_i = c ∫∫∫ F_i(n̄(X) diag(κ₁, κ₂))`. The identities `blockDiagGL_mul_dTail`
  and `blockLowerGL_mul_dTail` give `F_i(n̄(X) diag(κ₁, κ₂)) = c' Φ u_i h_i s κ₁ κ₂ X`. Hence
  `∫_U F_i = c c' tripleΦ u_i h_i s`. The hypothesis at `s'` says `∑_i ∫_U F_i = 0`, so
  `c c' ∑_i tripleΦ u_i h_i s = 0`. Finally `c ≠ 0`, and `c' ≠ 0` because
  `norm_principalSeriesCharacter` gives `|c'|` as a product of positive powers.
* `tendsto_tripleΦ` repeats the three dominated-convergence steps of
  `ComplexBlockLimit.integral_mul_blockStep_eq_zero`: the `X`-integral, then the `κ₂`-integral, then
  the `κ₁`-integral. The dominating function is `C_u C_h B_γ(X)` from `norm_Φ_le`, with
  `γ_l = max(Re e_{l+1} − Re e_l − 1, −2)`. It is integrable by `hT1` with the tail condition
  `tail_max`. Pointwise, `n̄((n+1)⁻¹X) → 1` and `u` is continuous.
* `sum_blockTerm_eq_zero`: `tendsto_finsetSum` gives
  `∑_i tripleΦ u_i h_i (n+1) → ∑_i blockTerm u_i h_i`. The sequence is identically `0` by
  `sum_tripleΦ_eq_zero`, and limits in `ℂ` are unique.
* `blockTerm_eq_of_integral_eq` applies `sum_blockTerm_eq_zero` to the two pairs `(u₁, h₁)` and
  `(−u₂, h₂)`, indexed by `Bool`. The vanishing hypothesis is the given equality, by `integral_neg`.
  Since `blockTerm (−u₂) h₂ = −blockTerm u₂ h₂`, the conclusion is the required identity.
