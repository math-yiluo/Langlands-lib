# The real-place Fourier transform of a Schwartz function is a Schwartz function

Helper module for the dual side of the real equal-rank Rankin–Selberg integrals (Task 7400,
towards `Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`).
Authored by Worker 823. Every declaration is proved, with no axioms beyond Lean's standard ones.
The declarations are in the namespace `Langlands.Global.RankinSelbergGlobal.RealFourierSchwartz`.

The Library defines the Fourier transform at a real place
(`ArchimedeanLocal.realFourierTransform b Φ`, module `ArchimedeanIntegrals`) as

`Φ̂(x) = ∫_(ℝⁿ) Φ(y) · ψ_b(∑_j y_j x_j) dy`,

where `ψ_b = (realScaledCharacter b).complex` is `t ↦ exp(2πi b t)` and `dy` is the product of
`n` copies of the self-dual measure `(realSelfDualMeasure b).measure` on `ℝ`. The domain is
`Fin n → ℝ` with its sup norm. Mathlib's Schwartz-space Fourier transform
(`SchwartzMap.fourierTransformCLM`, notation `𝓕`) is defined only on real inner product spaces,
with `𝓕 f(w) = ∫ exp(−2πi ⟪v, w⟫) f(v) dv`. This module relates the two.

This is the standard fact that the Fourier transform maps the Schwartz space to itself, used by
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), whenever `Φ̂` appears in Theorem 2.1(iii)
(p. 6). It is implementation infrastructure; the definitions are the Library's and Mathlib's.

## Declarations

- `exists_pi_eq_smul_volume b`: there is `c ≥ 0` with
  `Measure.pi (fun _ => (realSelfDualMeasure b).measure) = c • volume` on `Fin n → ℝ`.
  Proof: the product of additive Haar measures is an additive Haar measure, and Mathlib's
  uniqueness theorem `Measure.isAddLeftInvariant_eq_smul` gives the constant. The value of `c`
  is not computed.
- `euclidEquiv n`: the continuous linear equivalence `EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ)`
  (`PiLp.continuousLinearEquiv`). It is the identity on coordinates.
- `scaleEquiv n b`: the continuous linear equivalence `(Fin n → ℝ) ≃ EuclideanSpace ℝ (Fin n)`,
  `x ↦ −b · x`. `scaleEquiv_apply` gives its coordinates `−b x_j`.
- `realFourierTransform_eq`: if the product measure is `c • volume`, then for every function
  `Φ` and every `x`,

  `realFourierTransform b Φ x = c · 𝓕(Φ ∘ euclidEquiv n)(scaleEquiv n b x)`.

  Proof: pull the constant out of the integral (`integral_smul_nnreal_measure`). Change
  variables from `Fin n → ℝ` to Euclidean space; this map preserves volume
  (`EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`). Then compare integrands:
  `ψ_b(∑_j v_j x_j) = exp(2πi b ∑_j v_j x_j)` and
  `exp(−2πi ⟪v, −b x⟫) = exp(2πi b ∑_j v_j x_j)`.
- `exists_schwartz_eq b Φ`: for every Schwartz function `Φ` on `Fin n → ℝ` there is a Schwartz
  function `Ψ` on `Fin n → ℝ` with `⇑Ψ = realFourierTransform b Φ`. Take
  `Ψ = c • ((𝓕 Φ_V) ∘ scaleEquiv n b)`, where `Φ_V = Φ ∘ euclidEquiv n`. Composition with a
  continuous linear equivalence preserves Schwartz functions
  (`SchwartzMap.compCLMOfContinuousLinearEquiv`), and so does `𝓕`. The values agree by
  `realFourierTransform_eq`.

The identity holds for every `n`, including `n = 0`, and no integrability hypothesis on `Φ` is
needed for `realFourierTransform_eq`, since both sides are Bochner integrals of the same
function after the change of variables.
