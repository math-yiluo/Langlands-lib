# Submodules of the dual principal series of `GL_n(ℂ)` and the Jacquet integral in stages

Lean module: `Langlands.Representation.Archimedean.ComplexJacquetDual`.

This module is infrastructure for the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the complex counterpart of the module
`JacquetDual` for `GL_n(ℝ)`, and follows its proof.

The module defines the Jacquet integral `Λ_n` on `GL_n(ℂ)` in stages and proves the dual
induction statement `D(n)` (`ComplexJacquetDual.jacquet_eq_zero`), the core of the
Langlands-lemma argument for the Langlands quotient of strictly dominant principal series. The
main statement is `Langlands.Archimedean.ComplexJacquetDualStatement`, proved as
`Langlands.Archimedean.complexJacquetDual`.

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `unitaryCompact ℂ n` with the
Haar probability measure `ComplexDuality.unitaryHaar n`. `principalSeries`, `kFiniteFunctions`,
`Whittaker.rightTranslation` and `rightDerivative (matrixModel ℂ n) X` (the right derivative of a
smooth function along a complex matrix `X`, an element of the real Lie algebra of `GL_n(ℂ)`) are
the Library's. `iota`, `iotaLin` (`Y ↦ diag(Y, 0)`), `iotaGL` (`g ↦ diag(g, 1)`) come from
`ComplexMaximalParabolicIntegration`; `IsPhasePower`, `dualChar` (`χ⁻¹`), `shiftChar`
(`χ (|·|²)^{−1/2}`), `IsStrictlyDominant`, `jacquetStep` (`T`) and `jacquetStep_mem` from
`ComplexPartialJacquet`; `integral_mul_jacquetStep_eq_zero` from `ComplexJacquetLimit`.
Declarations without a prefix are in the namespace `Langlands.Archimedean.ComplexJacquetDual`.

## The Jacquet integral

`jacquet n h` is defined by recursion on `n`: `jacquet 0 h = h(1)`, and
`jacquet (m+1) h = jacquet m (T h)`, where `T h(g) = ∫_{ℂ^m} h(J(x,1) diag(g,1)) dx` is the
partial Jacquet integral. Up to the identification of the lower unipotent subgroup `N̄` with
iterated charts, this is the integral of `h` over `N̄`. (For a function `h` for which some partial
integral diverges, Lean's integral is `0`; the statement below only evaluates `jacquet` on
strictly dominant principal series, where every stage converges by `ComplexPartialJacquet`.)

## The statement

`ComplexJacquetDualStatement`: let `χ_l : ℂˣ → ℂ` and `e : ℕ → ℂ` satisfy
`χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}`, `χ_l(1) = 1`, `|χ_l(z/|z|)| = 1`, and `Re e_{l+1} < Re e_l`
whenever `l + 1 < n`. Let `U ≠ 0` be a subspace of the `U(n)`-finite functions of
`principalSeries ℂ n` of the characters `z ↦ χ_l(z)⁻¹`, stable under right translation by every
`k ∈ U(n)` and under `rightDerivative (matrixModel ℂ n) X` for every complex `n × n` matrix `X`.
Let `h` be a `U(n)`-finite function of `principalSeries ℂ n χ` with
`∫_{U(n)} u(k) h(k) dk = 0` for every `u ∈ U`. Then `jacquet n h = 0`.

Provenance. Derived, internal infrastructure: the dual form of the Langlands lemma (a nonzero
`(𝔤, K)`-submodule of the dual principal series pairs nontrivially with the Jacquet integral),
proved by induction in stages along the maximal parabolic subgroups `P_{m,1}`. No literature
claim beyond this standard argument.

## Restriction to the Levi factor

`restrictLevi u = u ∘ ι` with `ι(g) = diag(g, 1)`. Let `u` be a `U(m+1)`-finite function of the
principal series of `χ⁻¹`. Then `restrictLevi u` is a `U(m)`-finite function of the principal
series of `(shiftChar χ)⁻¹` on `GL_m(ℂ)` (`restrictLevi_mem`). This uses three facts:

* smoothness (`contMDiff_restrictLevi`, through the Library's `unitsExtension`,
  `contDiffOn_unitsExtension` and `contMDiff_of_contDiffOn`, with `ι` smooth);
* the character identity `principalSeriesCharacter_lastCases_dual`:
  `(χ⁻¹ δ^{1/2})_{m+1}(a, 1) = ((shiftChar χ)⁻¹ δ^{1/2})_m(a)`, from
  `(|a_i|²)^{m/2 − i} = (|a_i|²)^{1/2} (|a_i|²)^{(m−1)/2 − i}` and `χ_m(1) = 1`;
* finiteness: right translates of `u ∘ ι` by `U(m)` are restrictions of right translates of `u`
  by `ι(U(m)) ⊆ U(m+1)`.

Restriction commutes with right translations (`rightTranslation_restrictLevi`). For right
derivatives, `R(Y)(u ∘ ι) = (R(ι_lin Y) u) ∘ ι` with `ι_lin Y = diag(Y, 0)`
(`rightDerivative_restrictLevi`). The proof uses `rightDerivative_eq_fderiv_mul_left`, the fact
that both functions agree near `1` on invertible matrices, and the chain rule with
`fderiv ι 1 = ι_lin` (`hasFDerivAt_iota`). If `U ≠ 0` is `U(m+1)`-stable, then `U ∘ ι ≠ 0`
(`map_restrictLevi_ne_bot`): a nonzero `u ∈ U` is nonzero at some `κ ∈ U(m+1)`
(`ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn`), and then `(R(κ)u) ∘ ι` is nonzero at
`1`.

## Orthogonality invariance with the Haar probability measure

`integral_mul_eq_zero_of_orthogonal` restates the orthogonality invariance
`ComplexMatrixCoefficientAnalytic.matrixCoefficient_eq_zero` (applied to the dual principal series
with exponents `−e`, `IsPhasePower.dual`) for the measure `unitaryHaar n`: if `U` is
`(𝔤, K)`-stable and `∫ u h = 0` for all `u ∈ U`, then `∫ u(k g) h(k) dk = 0` for all `u ∈ U`
and all `g`. The measure used there is the pushforward of `unitaryHaar n` to
`Matrix.unitaryGroup` under `toUnitaryGroup` (`integral_map_toUnitaryGroup`).

## The induction `D(n)`

`jacquet_eq_zero`. Let `χ` be a phase power whose exponents satisfy `IsStrictlyDominant e (n − 1)`,
and let `U`, `h` be as in the statement. Then `jacquet n h = 0`. Proof by recursion on `n`.

* `n = 0`. `GL_0(ℂ)` is trivial, so the hypothesis reads `u(1) h(1) = 0` for a `u ∈ U` with
  `u(1) ≠ 0`.
* `n = m + 1`.
  1. By orthogonality invariance, `∫ u(κ g) h(κ) dκ = 0` for every `g` and `u ∈ U`.
  2. By `integral_mul_jacquetStep_eq_zero`, `∫_{U(m)} (u ∘ ι) · T h = 0` for every `u ∈ U`.
  3. `U ∘ ι` is a nonzero `(𝔤, K)`-stable subspace of the `U(m)`-finite principal series of
     `(shiftChar χ)⁻¹` (previous section).
  4. `T h` is a `U(m)`-finite function of the principal series of `shiftChar χ`
     (`jacquetStep_mem`), and `shiftChar χ` is a phase power (`IsPhasePower.shift`).
  5. The shifted exponents `e − 1/2` satisfy `IsStrictlyDominant` for `m − 1`
     (`isStrictlyDominant_shift`).
  6. `D(m)` gives `jacquet m (T h) = 0`, that is, `jacquet (m+1) h = 0`.

`complexJacquetDual` assembles the statement from `jacquet_eq_zero`.
