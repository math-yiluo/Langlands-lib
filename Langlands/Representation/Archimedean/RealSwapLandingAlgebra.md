# Landing of block multiplier composites: reduction to special parameters

Lean module: `Langlands.Representation.Archimedean.RealSwapLandingAlgebra`, namespace
`Langlands.Archimedean.RealSwapLandingAlgebra`.

## Role and provenance

This module is an internal step in the proof of
`Langlands.Archimedean.RealCharacterInducedFiltrationStatement`. It proves the
Library statement `RealSwapLandingInducedFirstStatement` (module `RealSwapLandingStatement`)
from a hypothesis `SpecialLanding`, defined here. `SpecialLanding` asks for the same landing
conclusion only at the parameters `δ = n + 2` with `n ∈ ℕ`, and only for some multipliers
there, not for all of them. Its proof is analytic and is in a separate module.

The idea of the reduction: the conclusion `Φ¹_k u (g) = 0` does not depend on which solutions
`μ₁`, `μ₀` of the recurrences are used, up to a nonzero factor, and it depends polynomially on
`δ`. A polynomial that vanishes at all `n + 2` is zero. This argument is internal to the
project. It formalizes no literature statement, so the module has no sources. All other
declarations are auxiliary lemmas proved here from Library results.

## Notation

- `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`. `O(N)` is the subgroup `unitaryCompact ℝ N`.
- `r_p(θ) = blockRotation N p θ` is the rotation in the coordinates `p, p + 1`.
- `Φ^p_j F (g) = blockFourierCoefficient N p j F g = ∫₀^{2π} F(r_p(θ) g) e^{-ijθ} dθ`. The
  integral has no factor `1/(2π)`.
- `coeff k F = ∫₀^{2π} F(θ) e^{-ikθ} dθ` is the Library's Fourier coefficient of a function on
  `ℝ` (`RealBlockFourierFinite`), so `Φ^p_k F (g) = coeff k (θ ↦ F(r_p(θ) g))`.
- `IsRecurrent δ ε μ` means `μ(k + 2)(δ + k) = (k + 2 - δ) μ(k)` for all `k ≡ ε (mod 2)`.
  `IsSymmetric ε σ μ` means `μ(-k) = σ μ(k)` for all `k ≡ ε (mod 2)`. Both are Library
  predicates of `RealBlockMultiplier`.
- `c : RealCharacterData` has parity `ε₁ = c.parity.val`. `d : ComplexCharacterData` has
  weight `m`, and `ℓ = |m|` (`d.weight.natAbs`). We write `ε₀ = ℓ + 1 + ε₁`. The standard
  module of `[d, c]` is `realStandardModule 3 [RealBlock.induced d, RealBlock.character c]`,
  with position characters `χ = realPositionCharacter [d, c]`.

## Declarations

### Fourier uniqueness for continuous functions

- `eq_zero_of_coeff_eq_zero`: a continuous `2π`-periodic `F : ℝ → ℂ` with all `coeff k F = 0`
  satisfies `F 0 = 0`. Proof: lift `F` to a continuous function on `AddCircle (2π)` with
  `AddCircle.liftIco`. Its Mathlib Fourier coefficients are the `coeff k F`, up to the factor
  `1/(2π)`, so they vanish. The Fourier series is then summable, and
  `hasSum_fourier_series_of_summable` shows the function is `0`.
- `coeff_sub`: `coeff` is additive on differences of continuous functions.
- `eq_of_blockFourierCoefficient_eq`: two continuous functions on `GL_N(ℝ)` with the same
  `Φ^p_k` at `g` for all `k` agree at `g`, for `p + 1 < N`. Apply the previous lemma to
  `θ ↦ F(r_p(θ) g) - G(r_p(θ) g)`.

### Linearity of block Fourier coefficients

- `blockFourierCoefficient_sum`, `blockFourierCoefficient_const_mul` and
  `blockFourierCoefficient_lincomb`: `Φ^p_k` commutes with finite linear combinations of
  continuous functions.
- `blockFourierCoefficient_zero_fun` and `blockFourierCoefficient_zero_fun'`: `Φ^p_k 0 = 0`,
  pointwise and as functions.
- `blockFourierCoefficient_sum_modes`: for `p + 1 < N`,
  `Φ^p_j (Σ_{i ∈ I} c_i Φ^p_i F)(x) = 2π c_j Φ^p_j F (x)` if `j ∈ I`, and `0` otherwise.
  Proof: `θ ↦ Φ^p_i F(r_p(θ) x)` is `Φ^p_i F(x)` times the exponential mode `expMode i`
  (Library `blockFourierCoefficient_blockRotation_mul`); then use the orthogonality of the
  exponential modes.

### Recurrent symmetric multipliers on a window

- `windowPoly ε M m` is the polynomial
  `∏_{r < m} (ε + 2r + 2 - X) · ∏_{m ≤ r < M} (X + ε + 2r)`. The lemma `eval_windowPoly`
  computes its value, and `windowPoly_succ` gives the recurrence
  `P_{m+1}(δ)(δ + ε + 2m) = (ε + 2m + 2 - δ) P_m(δ)`.
- `exists_eq_windowPoly` (window lemma): let `ε ∈ {0, 1}` and let `μ` solve the recurrence for
  `δ` on the class `ε`. Then there is `c` with `μ(ε + 2m) = c · windowPoly ε M m (δ)` for all
  `m ≤ M`. Proof: two cases.
  - If no factor `δ + ε + 2r` with `r < M` vanishes, recurse forward from `m = 0`.
  - Otherwise `δ = -(ε + 2r₀)`. Then no factor `ε + 2m + 2 - δ` vanishes, and we recurse
    backward from `m = M`.
- `extPoly ε σ M i` extends the window polynomials to the integers. It is `windowPoly ε M m`
  at `i = ε + 2m ≥ 0`, `σ · windowPoly ε M m` at `i = -(ε + 2m) < 0`, and `0` off the class.
- `exists_eq_extPoly` (symmetric window lemma): if `μ` also satisfies `IsSymmetric ε σ μ`, then
  `μ i = c · extPoly ε σ M i (δ)` for all `i` of the class with `|i| ≤ ε + 2M`. Moreover
  `c ≠ 0` when `μ ε ≠ 0`.

### Bilinear window sums

- `windowSumPoly ε₀ ε₁ σ₀ σ₁ ℓ M₀ M₁ I₀ I₁ B` is the polynomial
  `Σ_{j ∈ I₀} extPoly ε₀ σ₀ M₀ j (X + ℓ) · Σ_{i ∈ I₁} extPoly ε₁ σ₁ M₁ i (X) · B i j`.
  The lemma `eval_windowSumPoly` computes its value at `δ`.
- `window_sum_eq` (window sums): let the windows satisfy `|j| ≤ ε₀ + 2M₀` on `I₀` and
  `|i| ≤ ε₁ + 2M₁` on `I₁`. Assume:
  - `B i j = 0` for `i` off the class `ε₁`;
  - `Σ_{i ∈ I₁} ν i B i j = 0` for `j` off the class `ε₀`, whenever `ν` satisfies
    `IsSymmetric ε₁ σ₁ ν`.

  Let `ν₁` solve the recurrence for `δ` on the class `ε₁`, and `ν₀` the recurrence for `δ + ℓ`
  on the class `ε₀`, with symmetry signs `σ₁` and `σ₀`. Then
  `Σ_{j ∈ I₀} ν₀ j Σ_{i ∈ I₁} ν₁ i B i j = c₀ c₁ · windowSumPoly … (δ)`. Here `c₀ ≠ 0` if
  `ν₀ ε₀ ≠ 0`, and `c₁ ≠ 0` if `ν₁ ε₁ ≠ 0`. Proof: substitute `exists_eq_extPoly` on the
  classes. Off the classes, the two vanishing hypotheses kill the terms.
- `eval_eq_zero_of_nat`: a complex polynomial that vanishes at all `n + 2`, `n ∈ ℕ`, vanishes
  everywhere (`Polynomial.eq_zero_of_infinite_isRoot`).

### Expansion of a composite of two block multipliers

- `expansion`: assume the following.
  - `f` is continuous, and its `r_p`-modes `Φ^p_i f` vanish on `O(N)` for `|i| > D₁`.
  - For `|i| ≤ D₁`, the `r_q`-modes `Φ^q_j Φ^p_i f` vanish on `O(N)` for `|j| > D₀`.
  - `h` and `u` are continuous, with `Φ^p_k h = μ₁ k Φ^p_k f` and `Φ^q_k u = μ₀ k Φ^q_k h` on
    `O(N)`.

  Then for every block `r`, every `k` and every `g ∈ O(N)`,
  `Φ^r_k u (g) = (2π)⁻² Σ_{|j| ≤ D₀} μ₀ j Σ_{|i| ≤ D₁} μ₁ i Φ^r_k Φ^q_j Φ^p_i f (g)`.
  Proof: by Fourier uniqueness, `h` agrees on `O(N)` with the finite sum
  `h' = (2π)⁻¹ Σ_{|i| ≤ D₁} μ₁ i Φ^p_i f`, and `u` with
  `u' = (2π)⁻¹ Σ_{|j| ≤ D₀} μ₀ j Φ^q_j h'`. Block Fourier coefficients at points of `O(N)` only
  see values on `O(N)` (`RealSwapFLanding.blockFourierCoefficient_congr`). Linearity then gives
  the formula.

### Parity under the rotation by `π`

- `exp_int_mul_pi`: `exp(jπi) = (-1)^j`. `neg_one_zpow_eq_iff`:
  `(-1)^i = (-1)^e ↔ i - e` is even. `even_sub_iff_mod_two`: `k - e` is even if and only if
  `k - (e mod 2)` is even.
- `isRecurrent_mod_two` and `isSymmetric_mod_two`: the class `e` may be replaced by `e mod 2`.
- `blockFourierCoefficient_eq_zero_of_rotation_pi`: if `F(r_p(π) y) = τ F(y)` for all `y`, then
  `Φ^p_j F = 0` unless `(-1)^j = τ`.
- `sum_blockFourierCoefficient_rotation_pi`: let `f` be a principal series function on
  `GL_3(ℝ)` with characters `χ`. Let `ν(-i) = σ ν(i)` hold for all `i` with
  `(-1)^i = χ₁(-1) χ₂(-1)`. Then `H = Σ_{|i| ≤ D} ν i Φ¹_i f` satisfies
  `H(r_0(π) y) = χ₀(-1) χ₁(-1) σ H(y)`. Proof: `r_0(π)` is the sign matrix `diag(-1, -1, 1)`.
  The Library sign-reflection lemmas of `RealBlockFourierFinite` give
  `Φ¹_i f (r_0(π) y) = χ₀(-1) χ₁(-1) Φ¹_{-i} f (y)`. Then reindex `i ↦ -i`; the modes off the
  class vanish by parity.

### Reduction to the special parameters `δ = n + 2`

- `realPositionCharacter_induced_character_zero`, `_one`, `_two`: the position characters of
  `[d, c]` at `-1` are `(-1)^(ℓ+1)`, `1` and `(-1)^ε₁`.
- `SpecialLanding` (definition, a proposition): take any `c`, `d`, any `O(3)`-finite `f` in the
  standard module of `[d, c]`, and any `n ∈ ℕ`. Then there exist `μ₀`, `μ₁`, `h`, `u` with:
  - `IsRecurrent (n + 2) ε₁ μ₁` and `IsSymmetric ε₁ ((-1)^ε₁) μ₁`, with `μ₁ 0 ≠ 0` and
    `μ₁ 1 ≠ 0`;
  - `IsRecurrent (n + 2 + ℓ) ε₀ μ₀` and `IsSymmetric ε₀ ((-1)^ε₀) μ₀`, with `μ₀ 0 ≠ 0` and
    `μ₀ 1 ≠ 0`;
  - `h` and `u` continuous, with `Φ¹_k h = μ₁ k Φ¹_k f` and `Φ⁰_k u = μ₀ k Φ⁰_k h` on `O(3)`;
  - `Φ¹_k u = 0` on `O(3)` for `|k| < ℓ`.

  This is the hypothesis of `RealSwapLandingInducedFirstStatement`, specialized to
  `δ = n + 2`, for some multipliers that do not vanish at `0` and `1`.
- `landingPoly c d f D₀ D₁ k g` (definition) is `windowSumPoly` with classes `ε₀ mod 2` and
  `ε₁`, signs `(-1)^ε₀` and `(-1)^ε₁`, shift `ℓ`, windows `|j| ≤ D₀` and `|i| ≤ D₁`, and
  coefficients `B i j = Φ¹_k Φ⁰_j Φ¹_i f (g)`. It does not depend on `δ`, `μ₀`, `μ₁`, `h` or
  `u`.
- `exists_eq_landingPoly`: take the data of `RealSwapLandingInducedFirstStatement`, together with
  mode bounds `D₁` for `f` along `r_1` and `D₀` for the `Φ¹_i f`, `|i| ≤ D₁`, along `r_0`. Then
  for `g ∈ O(3)`, `Φ¹_k u (g) = (2π)⁻² c₀ c₁ · landingPoly (δ)`. Here `c₀ ≠ 0` if
  `μ₀ (ε₀ mod 2) ≠ 0`, and `c₁ ≠ 0` if `μ₁ ε₁ ≠ 0`. Proof: apply `expansion` with `p = 1`,
  `q = 0`, `r = 1`, then `window_sum_eq`. Its two vanishing hypotheses hold as follows.
  - `B i j = 0` off the class `ε₁`, because `Φ¹_i f = 0` there: Library
    `blockFourierCoefficient_eq_zero_of_parity`, with `χ₁(-1) χ₂(-1) = (-1)^ε₁`.
  - For symmetric `ν`, `Σ_i ν i B i j = Φ¹_k Φ⁰_j H (g)` with `H = Σ_i ν i Φ¹_i f`. By
    `sum_blockFourierCoefficient_rotation_pi`, `H(r_0(π) y) = (-1)^(ℓ+1) (-1)^ε₁ H(y)`, so
    `Φ⁰_j H = 0` for `j` off the class `ε₀`.
- `inducedFirst_of_special` (main theorem):
  `SpecialLanding → RealSwapLandingInducedFirstStatement`. Proof: fix the data, `g ∈ O(3)`
  and `|k| < ℓ`. Mode bounds `D₁` and `D₀` exist because `f` and its block coefficients are
  continuous and right `O(3)`-finite: Library `RealBlockJacquet.exists_bound`, and
  `RealSwapFLanding.mem_kFiniteVectors_blockFourierCoefficient`. We take `D₀` to be the
  supremum over `|i| ≤ D₁`. For each `n`, `SpecialLanding` gives data at `δ = n + 2` with
  `Φ¹_k u = 0`. By `exists_eq_landingPoly`, with nonzero factors, `landingPoly (n + 2) = 0`.
  Hence `landingPoly` vanishes identically (`eval_eq_zero_of_nat`). Then
  `exists_eq_landingPoly`, applied to the given data, gives `Φ¹_k u (g) = 0`.
