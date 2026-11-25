# Submodules of the dual principal series and the Jacquet integral in stages

Lean module: `Langlands.Representation.Archimedean.JacquetDual`.

This module defines the Jacquet integral `Λ_n` on `GL_n(ℝ)` in stages, and proves the dual
induction statement `D(n)` (`jacquet_eq_zero`). `D(n)` is the core of the Langlands-lemma
argument for the Langlands quotient of strictly dominant principal series.

Declarations without a prefix are in the namespace `Langlands.Archimedean.JacquetDual`.

## The Jacquet integral

`jacquet n h` is defined by recursion on `n`: `jacquet 0 h = h(1)`, and
`jacquet (m+1) h = jacquet m (T h)`, where `T` is the partial Jacquet integral
`PartialJacquet.jacquetStep`. Up to the identification of `N̄` with iterated charts, this is the
integral of `h` over the lower unipotent subgroup.

## Restriction to the Levi factor

`restrictLevi u = u ∘ ι` with `ι(g) = diag(g, 1)`. Let `u` be an `O(m+1)`-finite function of the
principal series of `χ⁻¹`. Then `restrictLevi u` is an `O(m)`-finite function of the principal
series of `(χ|·|^{−1/2})⁻¹` on `GL_m(ℝ)` (`restrictLevi_mem`). This uses three facts:

* smoothness (`contMDiff_restrictLevi`, through the Library's `unitsExtension` and
  `contMDiff_of_contDiffOn`);
* the character identity `principalSeriesCharacter_lastCases_dual`;
* finiteness: right translates of `u ∘ ι` by `O(m)` are restrictions of right translates of `u`.

Restriction commutes with right translations (`rightTranslation_restrictLevi`). For right
derivatives, `R(Y)(u ∘ ι) = (R(ι_lin Y) u) ∘ ι`, where `ι_lin Y = diag(Y, 0)`
(`rightDerivative_restrictLevi`). The proof uses `rightDerivative_eq_fderiv_mul_left`, the fact
that both functions agree near `1` on invertible matrices, and the chain rule with
`fderiv iota 1 = iotaLin` (`hasFDerivAt_iota`). If `U ≠ 0` is `O(m+1)`-stable, then
`U ∘ ι ≠ 0` (`map_restrictLevi_ne_bot`): a nonzero `u ∈ U` is nonzero at some `κ ∈ O(m+1)`,
and then `R(κ)u ∘ ι` is nonzero at `1`.

## Orthogonality invariance with Haar measure

`integral_mul_eq_zero_of_orthogonal` restates the orthogonality invariance
`MatrixCoefficientAnalytic.matrixCoefficient_eq_zero` for the measure `haarK n`. It is applied to
the dual principal series. The measure is the pushforward of `haarK n` to `Matrix.unitaryGroup`
under `toUnitaryGroup` (`integral_map_toUnitaryGroup`).

## The induction `D(n)`

`jacquet_eq_zero`. Let `χ` be a signed power whose exponents satisfy
`IsStrictlyDominant e (n − 1)`. Let `U ≠ 0` be a subspace of the `O(n)`-finite principal series
of `χ⁻¹` that is stable under right translation by `O(n)` and under all right derivatives. Let
`h` be an `O(n)`-finite function of the principal series of `χ` with `∫_{O(n)} u h = 0` for all
`u ∈ U`. Then `jacquet n h = 0`.

Proof by recursion on `n`.

* `n = 0`. `GL_0` is trivial, so the hypothesis reads `u(1) h(1) = 0` for a `u ∈ U` with
  `u(1) ≠ 0`.
* `n = m + 1`.
  1. By orthogonality invariance, `∫ u(κ g) h(κ) dκ = 0` for every `g`.
  2. By `JacquetLimit.integral_mul_jacquetStep_eq_zero`, `∫_{O(m)} (u ∘ ι) · T h = 0` for every
     `u ∈ U`.
  3. `U ∘ ι` is a nonzero `(𝔤, K)`-stable subspace of the `O(m)`-finite principal series of
     `(χ|·|^{−1/2})⁻¹`.
  4. `T h` is an `O(m)`-finite function of the principal series of `χ|·|^{−1/2}`
     (`PartialJacquet.jacquetStep_mem`).
  5. The shifted exponents satisfy `IsStrictlyDominant` for `m − 1`
     (`isStrictlyDominant_shift`).
  6. `D(m)` gives `jacquet m (T h) = 0`, that is, `jacquet (m+1) h = 0`.
