# The integration pairing on `U(n)`

Module: `Langlands.Representation.Archimedean.ComplexDuality.Pairing`.

## Purpose and provenance

This is internal infrastructure for the proof of
`Langlands.Archimedean.ComplexStandardDualityStatement`. It defines the standard pairing
`⟨f, h⟩ = ∫_{U(n)} f(k) h(k) dk` of the `U(n)`-finite functions of two principal series of
`GL_n(ℂ)`, for the Haar probability measure `unitaryHaar n` on `U(n) = unitaryCompact ℂ n`. It
proves the clauses of the target statement that need no differentiation: bilinearity, invariance
under right translation by `U(n)`, and nondegeneracy in the second argument. The remaining
`𝔤`-invariance clause is isolated as the proposition `IntegralLieInvariance`, and
`complexStandardDuality_of_lieInvariance` derives the target statement from it. The pairing is
the one named in the target statement's documentation. The module adds no literature claims and
cites no sources.

## Proof route

- **Bilinearity.** Functions in the principal series are smooth, hence continuous, and
  continuous functions on the compact group `U(n)` are integrable (`integrable_unitaryHaar`).
  Additivity of the integral therefore applies, and scalars move out with `integral_const_mul`.
- **`U(n)`-invariance.** The integrand of `⟨R(k) f, R(k) h⟩` is `x ↦ f(x k) h(x k)`, and
  `integral_mul_right_eq_self` for the right-invariant measure `unitaryHaar n` removes the
  translation.
- **Nondegeneracy.** By `exists_normSq_complexPositionCharacter`, the position characters of
  `ds` satisfy `|χᵢ(z)|² = |z|²^(sᵢ)`. For pointwise inverse characters,
  `exists_integral_mul_ne_zero` (module `GramWeight`) then provides `f` with `⟨f, h⟩ ≠ 0` for
  every `h ≠ 0`.
- **`𝔤`-invariance.** The value of the pairing at `(R(X) f, h)` and `(f, R(X) h)` unfolds by
  definition to the two integrals of `IntegralLieInvariance`, and this hypothesis says that
  their sum vanishes.

## Declarations

All declarations are in the namespace `Langlands.Archimedean.ComplexDuality`.

- `continuous_of_mem_kFiniteFunctions`: elements of
  `kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)` are continuous.
- `integrable_mul_of_continuous`: for continuous `f, h` on `GL_n(ℂ)`, the function
  `k ↦ f k * h k` on `U(n)` is integrable for `unitaryHaar n`.
- `integralPairing n χ χ'` (definition): the bilinear map
  `kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →ₗ[ℂ]
  kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n) →ₗ[ℂ] ℂ` sending `(f, h)` to
  `∫ k, f k * h k ∂(unitaryHaar n)`. `integralPairing_apply` states this value (by `rfl`).
- `integralPairing_rightTranslation`: `integralPairing` takes the same value on
  `(R(k) f, R(k) h)` as on `(f, h)`, for `k ∈ U(n)`. Here `R(k)` is
  `Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k`, and the membership proofs are
  the arbitrary ones that appear in the target statement.
- `IntegralLieInvariance` (proposition): for all `n`, all `χ, χ'` with `χᵢ(z) χ'ᵢ(z) = 1`, all
  `f ∈ principalSeries ℂ n χ`, `h ∈ principalSeries ℂ n χ'` and all
  `X ∈ Matrix (Fin n) (Fin n) ℂ`,
  `∫_{U(n)} (R(X) f) h + ∫_{U(n)} f (R(X) h) = 0` for `unitaryHaar n`. Here
  `R(X) = rightDerivative (matrixModel ℂ n) X`.
- `complexStandardDuality_of_lieInvariance`: `IntegralLieInvariance` implies
  `ComplexStandardDualityStatement`, with `Q = integralPairing n (complexPositionCharacter ds)
  (complexPositionCharacter ds')`.
