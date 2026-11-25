# Matrix coefficients related by transposition and the Jacquet integral

Lean module: `Langlands.Representation.Archimedean.ComplexReverseRecursion`, namespace
`Langlands.Archimedean.ComplexReverseRecursion`. It is a helper
for `ComplexStrictReverseIntertwinerKernelStatement` (module `ComplexReverseIntertwinerStrict`).

Notation as in `ComplexJacquetDual` and `ComplexJacquetLimitSum`. `GL_n(ℂ)` is
`Langlands.GeneralLinear n ℂ`, `U(n)` is `unitaryCompact ℂ n` with Haar probability measure
`ComplexDuality.unitaryHaar n`. `ι(g) = diag(g, 1)` is `iotaGL g`, `d(s) = diag(1, …, 1, s)` is
`dlastGL s`, `gᵀ` is `ComplexReverseTwist.transposeGL g`. `IsPhasePower χ e`,
`IsStrictlyDominant e m` and `dualChar χ` (the characters `z ↦ (χ_l z)⁻¹`) come from
`ComplexPartialJacquet`. `jacquet n` is the Jacquet integral in stages of `ComplexJacquetDual`
(`jacquet 0 h = h 1`, `jacquet (m+1) h = jacquet m (jacquetStep h)`), written `Λ_n` below;
`restrictLevi u = u ∘ ι`.

## Results

- `iota_transpose`, `transposeGL_iotaGL` (`ι(g)ᵀ = ι(gᵀ)`), `transposeGL_dlastGL`
  (`d(s)ᵀ = d(s)`).
- `integral_mul_swap` (the `GL_n(ℂ)`-invariance of the pairing). If `IsPhasePower χ e`, `w` lies in
  the principal series of `χ` and `u` in that of `dualChar χ`, then for every `g ∈ GL_n(ℂ)`
  `∫_{U(n)} w(κ g) u(κ) dκ = ∫_{U(n)} u(κ g⁻¹) w(κ) dκ`.
- `mul_jacquet_eq_of_transpose` (main result). Let `IsPhasePower χ e` and
  `IsStrictlyDominant e (n - 1)`. Let `x₁, x₂` be `U(n)`-finite functions in the principal series
  of `dualChar χ` and `y₁, y₂` `U(n)`-finite functions in the principal series of `χ`. If
  `∫_{U(n)} x₁(κ g) y₁(κ) dκ = ∫_{U(n)} x₂(κ gᵀ) y₂(κ) dκ` for every `g ∈ GL_n(ℂ)`, then
  `x₁(1) Λ_n(y₁) = x₂(1) Λ_n(y₂)`.

## Proof

- `integral_mul_swap`: `F(y) = u(y g⁻¹) w(y)` lies in the principal series of the modulus
  character (`rightTranslation_mem_principalSeries`, `contMDiff_mul_fun`,
  `principalSeriesCharacter_dual_mul`), so its `U(n)`-integral is invariant under right
  translation by `g` (`ComplexKIntegralInvariance.integral_mul_eq`). This gives
  `∫ u(κ g⁻¹) w(κ) dκ = ∫ u(κ) w(κ g) dκ`.
- `mul_jacquet_eq_of_transpose`, by induction on `n`.
  - `n = 0`: `GL_0(ℂ)` is trivial, both integrals are `x_i(1) y_i(1)` and `Λ_0(y) = y(1)`.
  - `n = m + 1`: fix `g ∈ GL_m(ℂ)`. Apply the hypothesis at `d(s) ι(g)`; its transpose is
    `ι(gᵀ) d(s) = d(s) ι(gᵀ)` (`iotaGL_mul_dlastGL`). So the pairs
    `(R(ι g) x₁, y₁)` and `(R(ι gᵀ) x₂, y₂)` have equal matrix coefficients at every `d(s)`. The
    ray-form limit `ComplexJacquetLimitSum.integral_mul_jacquetStep_eq_of_ray` (strict dominance
    of `e_0, …, e_m`) gives
    `∫_{U(m)} x₁(ι(k g)) jacquetStep y₁ k dk = ∫_{U(m)} x₂(ι(k gᵀ)) jacquetStep y₂ k dk`.
    This is the hypothesis of the case `m` for `restrictLevi xᵢ` (in the dual principal series of
    the shifted characters, `restrictLevi_mem`) and `jacquetStep yᵢ` (in the principal series of
    the shifted characters, `jacquetStep_mem`), with the shifted exponents still strictly dominant
    (`isStrictlyDominant_shift`). The induction hypothesis gives
    `x₁(ι(1)) Λ_m(jacquetStep y₁) = x₂(ι(1)) Λ_m(jacquetStep y₂)`, which is the claim since
    `ι(1) = 1` and `Λ_{m+1}(y) = Λ_m(jacquetStep y)`.

## Provenance

Derived (internal). The recursion follows the stepwise limit argument of the published modules
`ComplexJacquetLimit` and `ComplexJacquetDual`, applied to two pairs of functions
whose matrix coefficients agree after transposition. No statement from the literature is
introduced; all results are proved here.
