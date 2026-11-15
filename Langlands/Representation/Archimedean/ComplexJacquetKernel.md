# Proper submodules of strictly dominant complex principal series lie in the kernel of the Jacquet integral

Lean module: `Langlands.Representation.Archimedean.ComplexJacquetKernel`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the complex counterpart of Worker 5220's module
`JacquetKernel` for `GL_n(ℝ)` (Task 6749) and follows its proof, except that the nonzero
annihilator comes directly from the published `ComplexPrincipalSeriesAnnihilator`.

For strictly dominant phase-power characters `χ` of `GL_n(ℂ)` the module shows that the Jacquet
integral `Λ_n` (`ComplexJacquetDual.jacquet`) is linear on the `U(n)`-finite principal series and
vanishes on every proper `(𝔤, K)`-stable subspace (`ComplexJacquetKernel.jacquet_eq_zero_of_proper`).
The main statement is `Langlands.Archimedean.ComplexJacquetKernelStatement`, proved as
`Langlands.Archimedean.complexJacquetKernel`.

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `unitaryCompact ℂ n` with the
Haar probability measure `ComplexDuality.unitaryHaar n`. `principalSeries`, `kFiniteFunctions`,
`Whittaker.rightTranslation` and `rightDerivative (matrixModel ℂ n) X` are the Library's.
`IsPhasePower`, `dualChar` (`χ⁻¹`), `IsStrictlyDominant`, `jacquetStep`, `jacquetStep_mul`,
`integrable_chart` and `jacquetStep_mem` come from `ComplexPartialJacquet`; `jacquet`,
`isStrictlyDominant_shift` and `jacquet_eq_zero` from `ComplexJacquetDual`. Declarations without
a prefix are in the namespace `Langlands.Archimedean.ComplexJacquetKernel`.

## The statement

`ComplexJacquetKernelStatement`: let `χ_l : ℂˣ → ℂ` and `e : ℕ → ℂ` satisfy
`χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}`, `χ_l(1) = 1`, `|χ_l(z/|z|)| = 1`, and `Re e_{l+1} < Re e_l`
whenever `l + 1 < n`. Let `W` be a subspace of the `U(n)`-finite functions of
`principalSeries ℂ n χ`, stable under right translation by every `k ∈ U(n)` and under
`rightDerivative (matrixModel ℂ n) X` for every complex `n × n` matrix `X`, and suppose some
`U(n)`-finite function `f` of `principalSeries ℂ n χ` is not in `W`. Then `jacquet n w = 0` for
every `w ∈ W`.

Provenance. Derived, internal infrastructure: the Langlands lemma for strictly dominant
principal series (the Jacquet integral vanishes on proper submodules), from the dual statement
`ComplexJacquetDualStatement` and the annihilator of a proper submodule. No literature claim
beyond this standard argument.

## Linearity of the Jacquet integral

* `jacquetStep_smul`, `jacquet_smul`: `T(c h) = c T h` and `Λ_n(c h) = c Λ_n(h)`, for every `h`.
* `jacquetStep_add`: `T(h₁ + h₂) = T h₁ + T h₂` for `h₁, h₂` in the principal series of a
  strictly dominant phase power. Both sides transform by the same character under
  `diag(a) u` (`jacquetStep_mul`), so it suffices to compare them at `k ∈ U(m)`
  (`ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary`), where the integrals
  converge (`integrable_chart`) and `integral_add` applies.
* `jacquet_add`: `Λ_n(h₁ + h₂) = Λ_n(h₁) + Λ_n(h₂)` for `U(n)`-finite `h₁, h₂`, by induction on
  `n` with `jacquetStep_mem` (the stages stay in strictly dominant principal series).
* `jacquetKernel n hχ he`: the subspace of `U(n)`-finite principal-series functions `f` with
  `jacquet n f = 0`.

## The annihilator

`annihilator χ W hW` is the subspace of `U(n)`-finite functions `u` of the principal series of
`χ⁻¹` with `∫_{U(n)} u(k) w(k) dk = 0` for every `w ∈ W` (closed under sums and scalars by
integrability of continuous functions on `U(n)`, `ComplexDuality.integrable_mul_of_continuous`).

* `annihilator_rightTranslation`: it is stable under right translation by `k ∈ U(n)`, because the
  Haar measure is right invariant (`integral_mul_right_eq_self`) and `W` is stable under `k⁻¹`.
* `annihilator_rightDerivative`: it is stable under every right derivative `R(X)`, by the
  Library's infinitesimal invariance `ComplexDuality.integral_rightDerivative_mul_add_eq_zero`:
  `∫ (R(X) u) w + ∫ u (R(X) w) = 0` for `u` in the principal series of `χ⁻¹` and `w` in that of
  `χ`; the second integral vanishes because `R(X) w ∈ W`.
* `annihilator_ne_bot`: if some `U(n)`-finite `f` is not in `W`, the annihilator is nonzero. This
  is `ComplexPrincipalSeriesAnnihilator.exists_dual_annihilator` with `χ' = χ⁻¹`; its hypothesis
  `|χ_l(z)⁻¹|² = (|z|²)^{s_l}` holds with `s_l = −2 Re e_l` (`normSq_dualChar`).

## Proper submodules

`jacquet_eq_zero_of_proper`: if `W` is `(𝔤, K)`-stable and some `U(n)`-finite `f` is not in `W`,
then `W ⊆ jacquetKernel`. For `w ∈ W`, apply `ComplexJacquetDual.jacquet_eq_zero` to `h = w` and
`U = annihilator χ W hW`, which is nonzero, `(𝔤, K)`-stable, contained in the dual principal
series, and orthogonal to `w` by definition.

`complexJacquetKernel` assembles the statement from `jacquet_eq_zero_of_proper`.
