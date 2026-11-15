# The `O(a+k)`-integral in coordinates of the maximal parabolic subgroup `P_{a,k}` of `GL_{a+k}(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealBlockParabolicIntegrationStatement`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
states one proposition and proves nothing (two determinant lemmas used to build the matrices are
proved). The proposition is the integration formula needed for the Langlands lemma along the
maximal parabolic subgroup `P_{a,k}` (upper block triangular, blocks of sizes `a` and `k`); see
"Use". It is the real analogue of `ComplexBlockParabolicIntegrationStatement` (module
`ComplexBlockParabolicIntegrationStatement`, Worker 140, Task 7063), and for `k = 1` it is
equivalent to the published `MaximalParabolicIntegrationStatement`.

## Definitions

In the namespace `Langlands.Archimedean.RealBlockParabolic`; `Fin (a+k)` is identified with
`Fin a ⊕ Fin k` by `finSumFinEquiv` (the first `a` indices, then the last `k`).

* `blockLower X = [[1, 0], [X, 1]]` for `X ∈ M_{k×a}(ℝ)` (`Matrix.fromBlocks 1 0 X 1`, reindexed);
  `det_blockLower`: its determinant is `1`; `blockLowerGL X` is it as an element of
  `GL_{a+k}(ℝ) = Langlands.GeneralLinear (a+k) ℝ`. These elements form the opposite unipotent
  radical `N̄_P` of `P_{a,k}`.
* `blockDiag A D = [[A, 0], [0, D]]`; `det_blockDiag`: `det = det A · det D`;
  `blockDiagGL g₁ g₂ = diag(g₁, g₂) ∈ GL_{a+k}(ℝ)` for `g₁ ∈ GL_a(ℝ)`, `g₂ ∈ GL_k(ℝ)`.

## The statement

`RealBlockParabolicIntegrationStatement`: for all `a, k ∈ ℕ` there is a real `c > 0` such that
for every `F : GL_{a+k}(ℝ) → ℂ` which is smooth (`ContMDiff` for the manifold structure
`matrixModel ℝ (a+k)` of `GL_{a+k}(ℝ)`) and satisfies
`F(diag(z) u g) = ∏ᵢ |zᵢ|^{(a+k−1) − 2i} F(g)` for all `z ∈ (ℝˣ)^{a+k}`, `u` upper unipotent
and `g` (the published `MaximalParabolicIntegration.IsModulusCovariant`: `F` lies in the smooth
principal series of the modulus character of the upper triangular Borel subgroup),

1. for all `κ₁ ∈ O(a)` and `κ₂ ∈ O(k)` (`unitaryCompact ℝ a`, `unitaryCompact ℝ k`) the function
   `X ↦ F(n̄(X) diag(κ₁, κ₂))` is integrable on `Fin k → Fin a → ℝ` (Lebesgue measure; `X` read as
   a matrix by `Matrix.of`), and
2. `∫_{O(a+k)} F(κ) dκ = c · ∫_{O(a)} ∫_{O(k)} ∫_{M_{k×a}(ℝ)} F(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁`,

where the integrals over the orthogonal groups use the Haar probability measures
`RealPrincipalSeriesDuality.haarK` (for the Borel σ-algebra `measurableSpaceK`).

Edge cases: for `a = 0` or `k = 0` the space `Fin k → Fin a → ℝ` is a single point of measure `1`,
`O(0)` is trivial, and the formula holds with `c = 1`. For `k = 1`, after the substitution
`X ↦ κ₂ X κ₁⁻¹` (which preserves Lebesgue measure), it is the published
`MaximalParabolicIntegrationStatement` (in the form with `κ₁` outside, used in the published
`JacquetLimit` as `integral_eq_chart'`), with the explicit Gaussian constant there.

## Provenance

Derived; the standard integration formula relating the Haar measure of `K = O(a+k)` to the
Lebesgue measure of `N̄_P × K_M` on the modulus-induced functions (the integration formula for
`G = N̄_P P` up to a null set), in the Library's normalizations. No specific literature statement
is claimed; the constant `c` is not identified.

Why it is true: (i) average `F` over `K_M = O(a) × O(k)` on the left,
`F^♮(g) = ∫_{K_M} F(m g) dm`; by the published `KIntegralInvariance` for `GL_a(ℝ)` and `GL_k(ℝ)`
the average is left `P_{a,k}`-covariant with the modulus character of `P_{a,k}`, and
`∫_K F = ∫_K F^♮`; (ii) for continuous functions in the principal series of the modulus character of
`P_{a,k}` the `K`-integral is a positive multiple of the `N̄_P`-integral (both are
`G`-invariant functionals on this one-dimensionally-normalized space; for `F^♮` this is the
Gaussian/chart computation of `MaximalParabolicIntegration` with `k` rows instead of one);
(iii) `F^♮(n̄(X)) = ∫_{K_M} F(n̄(κ₂ X κ₁⁻¹) diag(κ₁, κ₂)) dκ` because
`diag(κ₁, κ₂) n̄(X) = n̄(κ₂ X κ₁⁻¹) diag(κ₁, κ₂)`, and the substitution `X ↦ κ₂⁻¹ X κ₁` preserves
Lebesgue measure, so Fubini gives the order of integration of the statement. Integrability for
every (not only almost every) `κ₁, κ₂` follows from `|F(n̄(X) κ)| ≤ sup_K |F| · E(n̄(X))` with the
right-`K`-invariant spherical function `E` of the modulus character, whose `N̄_P`-integral is
finite by (ii) applied to `E`.

## Use

In Task 6749 the formula is applied to `F(y) = u(y a_t) h(y)` with `a_t = diag(1_a, e^t 1_k)`
central in the Levi factor, `h` in a principal series and `u` in its dual, to compute the leading
term of the `O(a+k)`-pairing along `a_t` (Langlands lemma along `P_{a,k}`). Since `a_t` commutes
with `diag(κ₁, κ₂)` and `n̄(X) a_t = a_t n̄(e^{-t} X)`, the limit `t → ∞` gives the pairing of `u`
restricted to the Levi factor with the partial Jacquet integral `∫ h(n̄(X) ·) dX`.
