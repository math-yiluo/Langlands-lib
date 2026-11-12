# Proof of the equal-rank change of additive character

Author: Worker 4803. Lean module:
`Langlands.Representation.RankinSelberg.EqualRankEpsilonCharacterChangeProof`,
namespace `Langlands.RankinSelberg`.

The module proves the published statement
`Langlands.RankinSelberg.EqualRankEpsilonCharacterChangeStatement.{uF, uV, uW}`
(module `EqualRankEpsilonCharacterChangeStatement`) as the theorem
`equalRankEpsilonCharacterChange`, at arbitrary independent universes `uF`
(field), `uV` (space of `π`) and `uW` (space of `σ`). It adds no hypothesis.
For irreducible admissible `π`, `σ` of `GL_n(F)`, `n = r + 1`, with central
characters `ω_π`, `ω_σ`, self-dual measures `ν` for `ψ` and `ν'` for
`ψ^a(x) = ψ(ax)`, and `ε(s, π × σ, ψ) = c q^(-ms)`, it gives
`ε(s, π × σ, ψ^a) = c' q^(-m's)` with `m' = m + n² ord a` and
`c' = c ω_π(a)^n ω_σ(a)^n |a|^(-n²/2)`.

The statement is internal and derived (see its Markdown). The proof follows
the section "Derivation" of the statement's Markdown, which adapts Jacquet
(2009), Remark 2.2, pp. 7–8, to the Library's p-adic integrals. Its six
obligations are met as listed at the end. The structure copies the published
unequal-rank proof (`UnequalRankEpsilonEquation.characterChange` in module
`PairFactorEpsilonTransport`, and module `PairFactorCharacterChangeProof`).
The equal-rank case adds the Fourier step and the central translation.

## Conventions

In Lean the rank is `n + 1`; below `n + 1` is the rank, so the statement's `r`
is `n`. `d_a = characterChangeElement a n = diag(a^n, …, a, 1)` (module
`Whittaker.CharacterChange`). `X(s) = q^(-s)` is `spectralPoint q s`. The
absolute value `abv` satisfies `|a| = q^(-o)`. `C = characterChangeScalar abv a n`
(module `EqualRankCharacterChange`) is the positive modulus by which left
translation by `d_a` scales a compatible quotient measure.
`S = Σ_{i ≤ n} (n - i)`, so `2S = n(n+1)` (`sum_fin_sub_mul_two`), and
`|det d_a| = q^(-oS)` (`abv_det_characterChangeElement_eq_zpow`, module
`PairFactorEpsilonTransport`). `ℓ_a = ℓ ∘ π(d_a)` and `ℓ'_a = ℓ' ∘ σ(d_a)` are
the translated functionals `characterChangeFunctional ψ π a ℓ` and
`characterChangeInverseFunctional ψ σ a ℓ'`.

## Generic part (any field with a topology, any absolute value)

Section `ModelFunctions` and `SecondDual`:

- `modelMap_characterChangeFunctional_self`: the model function of `v` for
  `ℓ_a` is the left translate by `d_a` of the model function for `ℓ`
  (`characterChangeFunction`, module `Whittaker.CharacterChange`). For `σ` this
  is the published `modelMap_characterChangeInverseFunctional` (module
  `UnequalRankDualCharacterChange`), which holds in any rank.
- `firstDual_modelMap_characterChangeFunctional_self`: the first dual function
  `g ↦ W(w ᵗg⁻¹)` (`firstDualFunction`, module `FunctionalEquationStatement`)
  of the translated model is `ω_π(a)^n` times the left translate by `d_a` of
  the first dual function of the original model. The proof uses
  `inverseTranspose_characterChangeElement` and
  `weylLong_mul_characterChangeElement_inv` (module
  `UnequalRankDualCharacterChange`): `w ᵗ(d_a h)⁻¹ = (a^n)⁻¹ · d_a · w ᵗh⁻¹`,
  and the scalar `(a^n)⁻¹` acts on `π` by `ω_π(a)^(-n)`. For `σ` this is the
  published `secondDual_modelMap_characterChangeInverseFunctional`.
- `modelMap_mul_scalar`, `firstDual_modelMap_mul_scalar`,
  `secondDual_modelMap_mul_scalar`: right translation by the scalar matrix `b`
  multiplies a model function by `ω(b)` and a dual function by `ω(b)⁻¹`
  (`inverseTranspose_scalar'`, module `UnequalRankDualCharacterChange`).

Section `Integrals` (on `N \ GL_(n+1)`, integrand `equalRankIntegrand`, module
`QuotientIntegrals`):

- `equalRankIntegral_congr_smul`: if the two functions are pointwise multiplied
  by `c` and `c'`, the integral is multiplied by `c c'`.
- `equalRankIntegral_smul_test`: the integral is linear in `Φ`.
- `lastRow_mul_scalar`: the last row of `g b` is `b` times the last row of `g`.
- `equalRankIntegral_central_translate`: the central translation. If right
  translation by every element preserves `μ` (this is
  `IsCompatible.right_invariant`, module `Analysis.Local.QuotientMeasure`, for
  every compatible quotient measure) and the scalar matrix `b` multiplies `W`,
  `W'` by `c`, `c'`, then
  `Ψ(s, W, W', Φ) = c c' |det b|^s Ψ(s, W, W', Φ(b ·))`. The proof changes
  variables `g ↦ g b` with `MeasurePreserving.integral_comp`, using
  `rightTranslate_mk` (module `Group.LeftQuotient`) and `determinantWeight_mul`
  (module `RankinSelberg.CharacterChange`). The Derivation's translation
  `g ↦ a⁻¹ g` is this one with `b = a`, since scalars are central.

Section `Fourier`:

- `dilateTest b Φ`: the Schwartz–Bruhat function `x ↦ Φ(b x)`, locally
  constant and compactly supported because `x ↦ b x` is a homeomorphism.
- `IsRowFourierPair.characterChange`: if `Φ̂` is the `ψ`-transform of `Φ` for
  `ν` (`IsRowFourierPair`, module `HarmonicAnalysis.RowFourier`), then
  `κ^(n+1) Φ̂(a ·)` is the `ψ^a`-transform of `Φ` for `κ ν`
  (`AdditiveHaarMeasure.scale`, module `HarmonicAnalysis.CharacterTransport`).
  The proof is the published `rowFourierIntegral_scale` (module
  `HarmonicAnalysis.RowFourierHaarSurjectivityProof`) and
  `ψ^a(Σ x_i y_i) = ψ(Σ x_i (a y_i))` (`rowPairing_smul_right`).

Section `Spans`:

- `zetaSpan_values_eq_of_monomial_test`: let two integral families `I₁`, `I₂`
  take model functions through surjective parametrizations by vectors, and
  let `I₂ = α X^k I₁` for one unit `α` and one `k`, for all vectors, tests and
  `s`. Then their sets of rational continuations span the same Laurent module.
  The proof uses `zetaSpan_eq_of_monomial_mul` and
  `HasRationalContinuation.monomial_mul` (module `LaurentTransport`).

Section `Constants`:

- `equalRankConstants_eq`: with `|a| = q^(-o)` and `κ² = |a|`,
  `|a|^(-(n+1)²/2) = κ^(n+1) q^(oS + o(n+1))`. The proof compares logarithms,
  using `ofReal_cpow_eq_exp` and `ofReal_pow_eq_exp` (module
  `PairFactorEpsilonTransport`) and `2S = n(n+1)`.

Section `ModelIntegrals`. The hypotheses are `q > 0`, the character-change
measure law `HasCharacterChangeMeasureLaw abv a μ` (module
`RankinSelberg.CharacterChange`), and `|det d_a| = q^(-k)`.

- `equalRankModelIntegral_characterChange`: the integral for `ψ^a`, `ℓ_a`,
  `ℓ'_a` and `Φ` is `C X^(-k)` times the integral for `ψ`, `ℓ`, `ℓ'` and `Φ`.
  After the two model identities this is the published
  `equalRankIntegral_characterChange_monomial` (module `EqualRankCharacterChange`).
- `dualEqualRankModelIntegral_characterChange`: the dual integral for `ψ^a`
  and `Φ` is `ω_π(a)^n ω_σ(a)^n C X^(-k)` times the dual integral for `ψ` and
  `Φ`. It applies the dual model identities, the equality of characters
  `(ψ⁻¹)^a = (ψ^a)⁻¹` (`UnitaryAdditiveCharacter.scale_scale`), and the same
  published monomial lemma for `ψ⁻¹`.
- `dualEqualRankModelIntegral_characterChange_dilate`: with `|a| = q^(-o)` and
  right invariance of `μ`, the dual integral for `ψ^a` and the test
  `t Φ(a ·)` is `ω_π(a)^(n+1) ω_σ(a)^(n+1) C t X^(-k - o(n+1))` times the dual
  integral for `ψ` and `Φ`. The central translation by `a` gives the extra
  factor `ω_π(a) ω_σ(a)` and `|det(a·1)|^s = X^(o(n+1))`
  (`abv_det_scalar`, module `PairFactorEpsilonTransport`;
  `determinantWeight_eq_spectralPoint_zpow`, module `EqualRankCharacterChange`).
  It also removes the dilation.

Section `Generic`, the main generic theorem:

- `EqualRankEpsilonEquation.characterChange`: from
  `EqualRankEpsilonEquation q ψ abv μ ν π σ ℓ ℓ' c m` (module `EpsilonFactor`)
  it derives `EqualRankEpsilonEquation q ψ^a abv μ (κ ν) π σ ℓ_a ℓ'_a c'
  (m + (n+1)² o)`, for any `c'` with
  `c' = c ω_π(a)^(n+1) ω_σ(a)^(n+1) |a|^(-(n+1)²/2)`. The hypotheses are
  `q > 0`, `|a| = q^(-o)`, the measure law and right invariance of `μ`,
  σ-finiteness of `ν`, `κ > 0` with `κ² = |a|`, and the central characters.
  Proof:
  - `ζ` is unchanged (`HasModelMinusOneScalar.characterChange`, module
    `PairFactorEpsilonTransport`).
  - By `modelMap_surjective` (module `Whittaker.Algebraic`), the two integral
    lemmas and `zetaSpan_values_eq_of_monomial_test`, the spans of the
    integrals and of the dual integrals for `ψ^a` are those for `ψ`. So the
    normalized generators `P` and `P^∨` are unchanged.
  - For model functions of `v`, `u` (every model function is one) and a test
    `Φ`, the equation for `ψ` gives `Φ̂`, `R`, `R^∨`. For `ψ^a` take the
    transform `κ^(n+1) Φ̂(a ·)` and the continuations
    `C X^(-oS) R` and `β X^(-oS - o(n+1)) R^∨`, with
    `β = ω_π(a)^(n+1) ω_σ(a)^(n+1) C κ^(n+1)`. The continuation property
    follows from `HasRationalContinuation.monomial_mul` and the integral
    lemmas.
  - `NormalizedFunctionalEquation.monomial_transport` (module
    `PairFactorCharacterChangeAlgebra`) transports the normalized functional
    equation. Its two side conditions are:
    - `m' + (-oS) = m - (-oS - o(n+1))`, that is
      `m' = m + o(2S + n + 1)`. This is `m' = m + (n+1)² o`, since
      `2S = n(n+1)`;
    - `c' C = c β q^(oS + o(n+1))`. The constant `C` cancels, and what remains
      is `equalRankConstants_eq`.

## p-adic assembly

Section `Padic` uses the local instances of module
`PairFactorCharacterChangeAssembly` (canonical topology, valuative relation,
local field structure, Borel measurable structures on `F`, `GL_(n+1)(F)`, the
upper unipotent group and the quotient). Its own local instances make the
quotient Borel and record second countability and σ-compactness of `F` from
the canonical topological data. σ-compactness gives the σ-finiteness of `ν`.

`equalRankEpsilonCharacterChange`. Fix the data of the statement and
`e = (c, m)` with `IsPadicSymmetricEpsilonFactor F ψ ν π σ e`. Set
`N = (r+1)²` and `c' = c ω_π(a)^(r+1) ω_σ(a)^(r+1) |a|^(-N/2)`, a unit by
`normalizedAbs_cpow_ne_zero` (module `PairFactorCharacterChangeAssembly`).
Take `e' = (c', m + N ord a)`; the two formulas of the conclusion hold by
definition. It remains to show the epsilon relation for `ψ^a` and `ν'`:

1. In equal rank `isPadicSymmetricEpsilonFactor_of_le` (module
   `PadicPairFactors`) and `isPairEpsilonFactor_self` (module `EpsilonFactor`)
   turn both relations into `IsEqualRankEpsilonFactor`.
2. `ν' = |a|^(1/2) ν` is `LocalFactor.PadicAbelian.SelfDualHaar.val_eq_scale`,
   with `κ = sqrtNormalizedAbs F a`, `κ > 0` and `κ² = |a|`
   (`sqrtNormalizedAbs_pos`, `sqrtNormalizedAbs_sq`; all in module
   `PairFactorCharacterChangeMeasures`).
3. The existence of a compatible quotient measure does not depend on `ψ`. The
   nonzero functionals for `ψ^a` are the images of those for `ψ` under
   `characterChangeFunctionalEquiv` and `characterChangeInverseFunctionalEquiv`
   (module `Whittaker.CharacterChange`); they stay nonzero by
   `val_ne_zero_of_linearEquiv` (module `PairFactorCharacterChangeAssembly`).
4. Let `μ` be compatible and `ℓ`, `ℓ'` nonzero functionals for `ψ^a`. Their
   preimages `ℓO`, `ℓO'` under the two equivalences are nonzero functionals for
   `ψ`, so the hypothesis gives the equation for `μ`, `ℓO`, `ℓO'`.
   `EqualRankEpsilonEquation.characterChange` applies with the following inputs.
   - `q > 0`, from `residueCardinality_gt_one`.
   - `|a| = q^(-ord a)`, from `normalizedAbs_of_ne_zero`.
   - The measure law of `μ`: `characterChangeCompatibleMeasure` (module
     `CharacterChangeMeasure`).
   - The right invariance of `μ`: `IsCompatible.right_invariant`.

   It gives the equation for `ψ^a`, `κ ν`, the translates of `ℓO`, `ℓO'`, `c'`
   and `m + N ord a`. The translates are `ℓ`, `ℓ'` (`apply_symm_apply`).

## Derivation obligations of the statement's Markdown

1. The compatible measure and the functionals for `ψ^a`: step 3 above.
2. The measure law: `characterChangeCompatibleMeasure`, step 4.
3. `ν' = |a|^(1/2) ν` and `Φ̂_a = |a|^(n/2) Φ̂(a ·)`: step 2 and
   `IsRowFourierPair.characterChange`. The function `Φ̂_a` is the
   Schwartz–Bruhat function `κ^(n+1) • dilateTest a Φ̂`.
4. Central translation: `equalRankIntegral_central_translate`. It uses the
   right invariance that is part of every compatible quotient measure.
5. The transport of the continuations and the unchanged generators `P`,
   `P^∨`: `zetaSpan_values_eq_of_monomial_test` and the integral lemmas. They
   are proved for the functional-level spans and every compatible `μ`.
6. The comparison of the monomials: the two side conditions of
   `monomial_transport`, with `equalRankConstants_eq`. Uniqueness is not
   needed: the proof builds the factor for `ψ^a` directly.

## Lean checks

`lean_check` with declaration
`Langlands.RankinSelberg.equalRankEpsilonCharacterChange`, Lake build:

- 0 errors and 0 warnings.
- A theorem with universe parameters `uF`, `uV`, `uW`, whose type is
  `EqualRankEpsilonCharacterChangeStatement.{uF, uV, uW}`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
