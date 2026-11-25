# High block modes after two block multipliers on `GL_3(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealSwapFLanding`, namespace
`Langlands.Archimedean.RealSwapFLanding`.

## Role and provenance

This module is an internal step in the proof of
`Langlands.Archimedean.RealCharacterInducedFiltrationStatement`. There, a
principal series function `f` on `GL_3(ℝ)` whose modes along the first rotation are small is
moved by two block multiplier maps, first along `r_1` and then along `r_0`. One must show that
the result has small modes along `r_1`. Call this the "F-landing" step.

The main theorem `highModes_eq_zero` derives this from the landing statement
`RealSwapLandingCharacterFirstStatement`, which it takes as a hypothesis. That statement is in
the Library module `RealSwapLandingStatement` and is not proved here. It concerns the other
direction: from the standard module of `[c, d]`, first along `r_0`, then along `r_1`. The proof
is a duality argument. We pair against test functions from the standard module of `[c, d]`,
then use the transposition rule and the orthogonality of complementary modes from
`RealBlockTransposition`.

The other declarations are auxiliary lemmas: the sign of the determinant, conjugates and
twists of block Fourier coefficients, block multipliers on `O(3)`-finite functions, reflected
multipliers, membership in the standard module of `[c, d]`, and a positivity lemma. All of them
are standard facts, proved here from Library results. No literature statement is formalized, so
the module has no sources.

## Notation

- `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`. `O(N)` is the subgroup `unitaryCompact ℝ N`, with
  the normalized Haar measure `RealPrincipalSeriesDuality.haarK N` (Library).
- `r_p(θ) = blockRotation N p θ` is the rotation in the coordinates `p, p + 1`.
- `Φ^p_j F (g) = blockFourierCoefficient N p j F g = ∫₀^{2π} F(r_p(θ) g) e^{-ijθ} dθ`.
- "Right `O(N)`-finite" means membership in
  `kFiniteVectors (Whittaker.rightTranslation ℂ (GL_N(ℝ))) (unitaryCompact ℝ N)`.
- `c : RealCharacterData`, `d : ComplexCharacterData` of weight `m`, and `ℓ = |m|`
  (`d.weight.natAbs`). `[c, d]` is the block list
  `[RealBlock.character c, RealBlock.induced d]`. Its standard module on `GL_3(ℝ)` is
  `realStandardModule 3 [c, d]`, and `χ` denotes its position characters
  `realPositionCharacter [c, d]`.
- `IsRecurrent` and `IsSymmetric` are the Library predicates of `RealBlockMultiplier`.

## Declarations

### The sign of the determinant

- `sgnDet N x = det x / |det x| ∈ {±1}`, as a complex number. This is the module's one
  definition.
- `det_ne_zero`, `continuous_sgnDet`, `sgnDet_mul` (multiplicative), `sgnDet_mul_self`
  (`sgnDet² = 1`), `sgnDet_pow_mul_self` (`(sgnDet^e)² = 1`), and `conj_sgnDet` (real valued).
- `sgnDet_blockRotation`: `sgnDet(r_p(θ)) = 1`. `sgnDet_blockRotation_mul`:
  `sgnDet(r_p(θ) x) = sgnDet(x)`.

### Twists, conjugates and block Fourier coefficients

- `blockFourierCoefficient_mul_sgnDet_pow`: `Φ^p_j (F · sgnDet^e)(g) = sgnDet(g)^e Φ^p_j F(g)`.
- `continuous_mul_sgnDet_pow` and `mem_kFiniteVectors_mul_sgnDet_pow`: the twist
  `F · sgnDet^e` of a continuous, respectively right `O(N)`-finite, function is again continuous,
  respectively right `O(N)`-finite.
- `blockFourierCoefficient_conj`: `Φ^p_j (conj F)(g) = conj (Φ^p_{-j} F (g))`.
- `blockFourierCoefficient_congr`: if `F₁ = F₂` on `O(N)`, then `Φ^p_j F₁ = Φ^p_j F₂` on `O(N)`.

### Block multipliers on `O(N)`-finite functions

- `mem_kFiniteVectors_blockFourierCoefficient`: for a continuous right `O(N)`-finite `F`, every
  `Φ^p_i F` is right `O(N)`-finite.
- `exists_multiplier` (**block multipliers**): let `p + 1 < N`, `F` continuous and right
  `O(N)`-finite, and `ν : ℤ → ℂ` any sequence. Then there is a continuous right `O(N)`-finite
  `F'` with `Φ^p_j F' = ν(j) Φ^p_j F` on `O(N)` for all `j`.

### Reflected multipliers

- `isRecurrent_comp_neg`: if `μ` solves `IsRecurrent δ ε`, so does `k ↦ μ(-k)`.
- `isSymmetric_comp_neg`: if `σ² = 1` and `μ` is `IsSymmetric ε σ`, so is `k ↦ μ(-k)`.
- `neg_one_pow_mul_self`: `(-1)^n (-1)^n = 1`.

### The standard module of `[c, d]`

- `realPositionCharacter_exp`: `χ_i(e^x) = e^{t_i x}` with `t_i = realPositionExponent ds i`,
  for any block list `ds`.
- `realInducedBlockAt_character_induced`: the only induction block of `[c, d]` sits at
  position `1`, and it is `d`.
- `mem_realStandardModule_character_induced` (**membership**): let `f` be in the principal series
  of `χ`. If `Φ¹_k f = 0` on `O(3)` for every `|k| < ℓ`, then `f` lies in the standard module of
  `[c, d]`.
- `conj_realPositionCharacter_signUnit` and `conj_principalSeriesCharacter_signUnit`: at sign
  matrices the position characters, and the principal series character built from them, take
  real values `±1`.

### Positivity

- `eq_zero_of_integral_mul_conj`: if `G` is continuous on `GL_N(ℝ)` and
  `∫_{O(N)} G · conj G = 0`, then `G = 0` on `O(N)`.

### Main theorem

`highModes_eq_zero` (**high modes after two block multipliers**). Assume
`RealSwapLandingCharacterFirstStatement`. Let `δ ∈ ℂ`. Let `μ₀` solve the recurrence for `δ` on
the parity class `ℓ + 1 + ε₁` with symmetry sign `(-1)^{ℓ + 1 + ε₁}`, where
`ε₁ = c.parity.val`. Let `μ₁` solve the recurrence for `δ + ℓ` on the class `ε₁` with sign
`(-1)^{ε₁}`. These are exactly the hypotheses on `μ₀, μ₁` in
`RealSwapLandingCharacterFirstStatement`. Let `e ∈ ℕ`, and let `f, g₁, g, G` be continuous right
`O(3)`-finite functions on `GL_3(ℝ)` such that on `O(3)`:

1. `Φ⁰_j f = 0` for `|j| ≥ ℓ`;
2. `Φ¹_j g₁ = μ₁(j) Φ¹_j f` and `Φ⁰_j g = μ₀(j) Φ⁰_j g₁` for all `j`;
3. `Φ¹_j G = Φ¹_j g` for `|j| ≥ ℓ` and `Φ¹_j G = 0` for `|j| < ℓ`.

Assume also that for `a ∈ (ℝˣ)³` and `κ ∈ O(3)`,

    G(diag(sgn a) κ) = χ(sgn a) · sgnDet(diag(sgn a))^e · G(κ),

where `χ(sgn a)` is `principalSeriesCharacter ℝ 3 χ (signUnit ∘ a)`. Then `Φ¹_j g = 0` on
`O(3)` for every `|j| ≥ ℓ`.

So `G` is the projection of `g` onto its modes `|j| ≥ ℓ` along `r_1`. The theorem says that
this projection is zero. The last hypothesis says that `G` transforms under the sign matrices
like the principal series of `[c, d]`, twisted by `sgnDet^e`. The proof of the target theorem
will choose `e` to fit the sign pattern of `g`. This theorem takes `G` and its equivariance as
hypotheses. It does not construct `G`.

## Proofs

`sgnDet` lemmas. `sgnDet_mul` uses `det(xy) = det x det y` and `|ab| = |a||b|`.
`sgnDet_mul_self` uses `(det x)² / |det x|² = 1`. `sgnDet_blockRotation` writes
`r_p(θ) = r_p(θ/2) r_p(θ/2)` (Library `blockRotation_add`) and applies the two previous lemmas.

`blockFourierCoefficient_mul_sgnDet_pow`. Inside the integral,
`sgnDet(r_p(θ) g) = sgnDet(g)` does not depend on `θ`, so it moves out as a constant.

`mem_kFiniteVectors_mul_sgnDet_pow`. Twisting is the linear map `T F = F · sgnDet^e`. The right
translate of `T F` by `k ∈ O(N)` is `sgnDet(k)^e · T(R_k F)`. So the span of the translates of
`T F` lies in the image under `T` of the span of the translates of `F`, which is
finite-dimensional.

`blockFourierCoefficient_conj`. Conjugation commutes with the integral (`integral_conj`), and
`conj (e^{-ijθ}) = e^{ijθ} = e^{-i(-j)θ}`.

`blockFourierCoefficient_congr`. For `x ∈ O(N)` every point `r_p(θ) x` of the integral lies in
`O(N)`.

`mem_kFiniteVectors_blockFourierCoefficient`. Let `W` be the span of the right translates of
`F` by `O(N)`. It is finite-dimensional, and all its elements are continuous. On `W`, `Φ^p_i` is
linear (Library `blockFourierCoefficient_add` and `blockFourierCoefficient_smul`; this is where
continuity is needed). Right translation commutes with `Φ^p_i` (Library
`blockFourierCoefficient_rightTranslation`). So the translates of `Φ^p_i F` lie in the image of
`W`.

`exists_multiplier`. By the Library lemma `exists_bound`, there is `D` with `Φ^p_j F = 0` on
`O(N)` for `|j| > D`. Take `F' = Σ_{|i| ≤ D} (2π)⁻¹ ν(i) Φ^p_i F`. This is continuous
(`continuous_blockFourierCoefficient`) and right `O(N)`-finite (previous lemma). For
`g ∈ O(N)`, the Library lemma `blockFourierCoefficient_blockRotation_mul` gives
`Φ^p_i F(r_p(θ) g) = e^{iiθ} Φ^p_i F(g)`. So `θ ↦ F'(r_p(θ) g)` is a trigonometric polynomial.
Its `j`-th coefficient is `ν(j) Φ^p_j F(g)` for `|j| ≤ D` and `0` otherwise
(`coeff_finset_sum_expMode`). In the second case `Φ^p_j F(g) = 0` as well.

`isRecurrent_comp_neg`. Apply the recurrence of `μ` at `-k - 2`, which has the right parity,
and rearrange. `isSymmetric_comp_neg`. `μ(-(-k)) = μ(k) = σ μ(-k)`, using `σ² = 1`.

`realPositionCharacter_exp`. Write `χ_i(x) = χ_i(sgn x) |x|^{t_i}` (Library
`realPositionCharacter_eq_signUnit_mul`). Here `sgn(e^x) = 1`, `χ_i(1) = 1`, and
`(e^x)^{t_i} = e^{t_i x}`.

`realInducedBlockAt_character_induced`. Compute `realInducedBlockAt` at `p = 0, 1, 2, ≥ 3`.

`mem_realStandardModule_character_induced`. By `mem_realStandardModule_iff`, we must show that
`Φ¹_k f = 0` on all of `GL_3(ℝ)` for `|k| < ℓ`, since the only induction block is `d` at
position `1`. There are two cases.

- `(-1)^k = χ_1(-1) χ_2(-1)`. For the induction block, `χ_1(-1) χ_2(-1) = (-1)^{ℓ + 1}`, so
  `k ≡ ℓ + 1 (mod 2)` and `k` lies in `window ℓ`. A principal series function is smooth and
  satisfies the exponential equivariance `IsExpEquivariant` of the Library module
  `RealBlockLeftDerivative`, with exponents `α_i = t_i + 1 - i` (`N = 3`). The position
  exponents of the induction block satisfy `t_1 - t_2 = ℓ`, so `α_1 - α_2 = ℓ + 1`. The Library
  propagation lemma `blockFourierCoefficient_window_eq_zero` then spreads the vanishing on
  `O(3)` of the window modes to all of `GL_3(ℝ)`.
- Otherwise `Φ¹_k f = 0` everywhere by the parity lemma
  `blockFourierCoefficient_eq_zero_of_parity`.

`conj_principalSeriesCharacter_signUnit`. The Library lemma
`JacquetKernel.principalSeriesCharacter_sign` writes the character at signs as a product of the
`χ_i(sgn a_i)`. Each factor is `1` or `χ_i(-1) = ±1`
(`realPositionCharacter_neg_one`), and is therefore real.

`eq_zero_of_integral_mul_conj`. `G · conj G = |G|²` is real. If `G(x) ≠ 0` at some
`x ∈ O(N)`, then the continuous nonnegative function `|G|²` on the compact group is not
identically zero. Its Haar integral is then positive
(`Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`), a contradiction.

`highModes_eq_zero`. Write `(φ, ψ) = ∫_{O(3)} φ ψ`.

1. *Test function.* Put `G' = G · sgnDet^e` and `φ(κ) = conj (G'(κ))` on `O(3)`. This `φ` is
   continuous. By the Library lemma
   `OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors`, `G'` restricted to
   `O(3)` is a polynomial in the matrix entries. So `φ` is one too (with conjugated
   coefficients), and its right translates span a finite-dimensional space
   (`TranslateFinite.finiteDimensional_span_eval`). The equivariance hypothesis, together with
   `sgnDet(s κ) = sgnDet(s) sgnDet(κ)` and `sgnDet(s)^{2e} = 1`, gives
   `G'(s κ) = χ(s) G'(κ)` for sign matrices `s`. Since `χ(s)` is real, `φ(s κ) = χ(s) φ(κ)`.
   The Library extension theorem `principalSeriesExtension` then gives a right `O(3)`-finite
   function `t` of the principal series of `χ` with `t = conj G'` on `O(3)`.
2. *`t` is in the standard module of `[c, d]`.* On `O(3)`, by the conjugation and twist lemmas,
   `Φ¹_j t = conj (sgnDet^e · Φ¹_{-j} G) = 0` for `|j| < ℓ`. Membership follows from
   `mem_realStandardModule_character_induced`.
3. *Landing.* By `exists_multiplier`, choose `t₀` with `Φ⁰_j t₀ = μ₀(-j) Φ⁰_j t`, and `u` with
   `Φ¹_j u = μ₁(-j) Φ¹_j t₀`, on `O(3)`. The reflected multipliers satisfy the same recurrences
   and symmetries (`isRecurrent_comp_neg` and `isSymmetric_comp_neg`). So the landing hypothesis
   applies to `t, t₀, u` and gives `Φ⁰_j u = 0` on `O(3)` for `|j| < ℓ`.
4. *Twisted test functions.* Put `ψ = t · sgnDet^e`, `ψ₀ = t₀ · sgnDet^e` and
   `ψ₁ = u · sgnDet^e`. They are continuous and right `O(3)`-finite. The twist multiplies all
   block Fourier coefficients by the same factor `sgnDet(x)^e`, so on `O(3)`
   `Φ⁰_j ψ₀ = μ₀(-j) Φ⁰_j ψ`, `Φ¹_j ψ₁ = μ₁(-j) Φ¹_j ψ₀`, `Φ⁰_j ψ₁ = 0` for `|j| < ℓ`, and
   `Φ¹_j ψ = 0` for `|j| < ℓ`.
5. *Duality chain.* By `RealBlockTransposition.integral_mul_eq_of_multiplier`:
   - along `r_1` with the indicator `ν(j) = 1` for `|j| ≥ ℓ`, `0` otherwise, applied to `g`,
     `G` and `ψ, ψ`: `(G, ψ) = (g, ψ)`. The hypotheses hold by item 3 of the theorem, by
     `Φ¹_j ψ = 0` for `|j| < ℓ`, and because `ν(-j) = ν(j)`;
   - along `r_0` with `μ₀`: `(g, ψ) = (g₁, ψ₀)`;
   - along `r_1` with `μ₁`: `(g₁, ψ₀) = (f, ψ₁)`.

   Finally, `(ψ₁, f) = 0` by `integral_mul_eq_zero_of_modes` along `r_0` with `l = ℓ`. Indeed,
   `Φ⁰_j ψ₁ = 0` for `|j| < ℓ`, and `Φ⁰_j f = 0` for `|j| ≥ ℓ`.
6. *Conclusion.* On `O(3)`, `ψ = conj G' · sgnDet^e = conj G · sgnDet^{2e} = conj G`, because
   `sgnDet` is real. So `∫_{O(3)} G · conj G = (G, ψ) = 0`. Then `G = 0` on `O(3)` by
   `eq_zero_of_integral_mul_conj`. For `|j| ≥ ℓ` and `x ∈ O(3)`,
   `Φ¹_j g(x) = Φ¹_j G(x) = Φ¹_j 0 (x) = 0`, using `blockFourierCoefficient_congr`.
