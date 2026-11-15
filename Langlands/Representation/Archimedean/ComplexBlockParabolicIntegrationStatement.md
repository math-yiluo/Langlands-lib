# The `U(a+k)`-integral in coordinates of the maximal parabolic subgroup `P_{a,k}` of `GL_{a+k}(ℂ)`

Lean module: `Langlands.Representation.Archimedean.ComplexBlockParabolicIntegrationStatement`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It states one proposition and proves nothing (two
determinant lemmas used to build the matrices are proved). The proposition is the integration
formula needed for the Langlands lemma along the maximal parabolic subgroup `P_{a,k}` (upper block
triangular, blocks of sizes `a` and `k`); see "Use".

## Definitions

In the namespace `Langlands.Archimedean.ComplexBlockParabolic`; `Fin (a+k)` is identified with
`Fin a ⊕ Fin k` by `finSumFinEquiv` (the first `a` indices, then the last `k`).

* `blockLower X = [[1, 0], [X, 1]]` for `X ∈ M_{k×a}(ℂ)` (`Matrix.fromBlocks 1 0 X 1`, reindexed);
  `det_blockLower`: its determinant is `1`; `blockLowerGL X` is it as an element of
  `GL_{a+k}(ℂ) = Langlands.GeneralLinear (a+k) ℂ`. These elements form the opposite unipotent
  radical `N̄_P` of `P_{a,k}`.
* `blockDiag A D = [[A, 0], [0, D]]`; `det_blockDiag`: `det = det A · det D`;
  `blockDiagGL g₁ g₂ = diag(g₁, g₂) ∈ GL_{a+k}(ℂ)` for `g₁ ∈ GL_a(ℂ)`, `g₂ ∈ GL_k(ℂ)`.

## The statement

`ComplexBlockParabolicIntegrationStatement`: for all `a, k ∈ ℕ` there is a real `c > 0` such that
for every `F` in `principalSeries ℂ (a+k) (modulusCharacter (a+k))` — the smooth functions on
`GL_{a+k}(ℂ)` with `F(diag(z) u g) = ∏ᵢ (|zᵢ|²)^{(a+k−1) − 2i} F(g)` for `u` upper unipotent
(`ComplexKIntegralInvariance.modulusCharacter` and the Library's `principalSeriesCharacter`) —

1. for all `κ₁ ∈ U(a)` and `κ₂ ∈ U(k)` (`unitaryCompact ℂ a`, `unitaryCompact ℂ k`) the function
   `X ↦ F(n̄(X) diag(κ₁, κ₂))` is integrable on `Fin k → Fin a → ℂ` (Lebesgue measure; `X` read as
   a matrix by `Matrix.of`), and
2. `∫_{U(a+k)} F(κ) dκ = c · ∫_{U(a)} ∫_{U(k)} ∫_{M_{k×a}(ℂ)} F(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁`,

where the integrals over the unitary groups use the Haar probability measures
`ComplexDuality.unitaryHaar`.

For `k = 1` this is, after the substitution `X ↦ κ₂ X κ₁⁻¹`, the Library's
`ComplexMaximalParabolicIntegration.integral_eq_chart` (in the form
`ComplexJacquetLimit.integral_eq_chart'`). For `a = 0` or `k = 0` it holds with `c = 1`.

## Provenance

Derived; the standard integration formula relating the Haar measure of `K = U(a+k)` to the
Lebesgue measure of `N̄_P × K_M` on the modulus-induced functions (the Iwasawa/Bruhat integration
formula for `G = P N̄_P` up to a null set), in the Library's normalizations. No specific literature
statement is claimed; the constant `c` is not identified.

Intended proof (generalizing `ComplexMaximalParabolicIntegration` from one row to `k` rows):
(i) average `F` over `U(a) × U(k)` on the left; by `ComplexKIntegralInvariance` for `GL_a` and
`GL_k` the average is left `P_{a,k}`-equivariant with the modulus character of `P_{a,k}`;
(ii) such a function on `U(a+k)` depends only on the last `k` rows `R = [R₁, R₂]` of `κ`, through
`|det R₂|` and `R₂⁻¹ R₁`; (iii) the last `k` rows of a Haar-random unitary matrix are distributed like
the orthonormalized rows `(G Gᴴ)^{-1/2} G` of a standard complex Gaussian `G ∈ M_{k×(a+k)}`
(right `U(a+k)`-invariance of the Gaussian and completion of orthonormal `k`-frames to unitary
matrices, generalizing `ComplexLastRowIntegral`); (iv) in the chart `G = B [X, 1]` with
`B ∈ M_k(ℂ)`, Lebesgue measure is `|det B|^{2a} dB dX`, and the `B`-integral of
`|det B|^{p} e^{−tr(B (1 + X Xᴴ) Bᴴ)}` is `det(1 + X Xᴴ)^{−k−p/2}` times a positive constant
(substitution `B ↦ B (1 + X Xᴴ)^{−1/2}`).

## Use

In Task 7063 the formula is applied to `F(y) = u(y a_t) h(y)` with `a_t = diag(1_a, t·1_k)` central
in the Levi factor, `u` in a principal series and `h` in its dual, to compute the leading term of the
`U(a+k)`-pairing along `a_t` (Langlands lemma along `P_{a,k}`). Since `a_t` commutes with
`diag(κ₁, κ₂)` and `n̄(X) a_t = a_t n̄(t⁻¹X)`, the limit `t → ∞` gives the pairing of `u` restricted
to the Levi factor with the partial Jacquet integral `∫ h(n̄(X) ·) dX`.
