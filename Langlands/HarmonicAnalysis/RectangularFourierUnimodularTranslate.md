# Rectangular Fourier integrals of two-sided unimodular translates

Module `Langlands.HarmonicAnalysis.RectangularFourierUnimodularTranslate`.
Author: Worker 1117.

This module proves that the raw plus-sign rectangular Fourier integral
commutes with two-sided multiplication by invertible matrices of normalized
determinant one, after the matrices are replaced by their inverse transposes.
It is a helper for the transformed side of the two-block functional equation
(Godement–Jacquet, *Zeta Functions of Simple Algebras* (1972), proof of
Theorem 3.4, printed 36–45). There a compact-subgroup translate
`x ↦ Φ (k⁻¹ * x * k')` of a test function is expanded as a finite sum, and the
same expansion is needed for the Fourier transform. The source uses this
compatibility without stating it as a lemma. The module introduces no
definitions.

Throughout, `F : PadicField p` carries an arbitrary topological datum `T`
(not necessarily the canonical one). The topology on `F.Carrier` is
`T.topology` and the measurable structure is `borel F.Carrier`. `ψ` is any
unitary additive character and `ν` any additive Haar measure; self-duality is
not used. `GeneralLinear.inverseTranspose n F.Carrier g` is `(g⁻¹)ᵀ`, written
`Aᵀ⁻¹` below. `rectangularPairing x y = ∑ i j, x i j * y i j` is the entrywise
pairing, and `rectangularFourierIntegral ψ ν f y = ∫ x, f x * ψ (rectangularPairing x y)`
with respect to `rectangularMeasure ν r s`.

## Results and proofs

- The imported `PadicField.TopologicalData.determinantNorm_eq_one_of_mem_compact`
  from `Group.GL.NormalizedCharacter` supplies determinant norm one for every
  element of a compact matrix subgroup. It applies the existing continuous
  positive-character theorem; no separate compact-subgroup proof is defined here.
- `measurePreserving_rectangular_mul_mul`: for `A ∈ GL_r(F)` and
  `B ∈ GL_s(F)` with `T.determinantNorm r A = 1` and
  `T.determinantNorm s B = 1`, the map `X ↦ A * X * B` preserves
  `rectangularMeasure ν r s`. Proof: the published Haar scaling theorem
  `padicRectangularHaarScaling` for `A` and `B⁻¹` says that the image measure is
  `(|det A|^s / |det B⁻¹|^r)⁻¹` times the original one, and this factor is `1`.
- `rectangularPairing_mul_mul`: for all invertible `A`, `B` and all `x`, `y`,
  `rectangularPairing (A x B) (Aᵀ⁻¹ y Bᵀ⁻¹) = rectangularPairing x y`. Proof:
  the pairing is `trace (x * yᵀ)`. The transpose of `Aᵀ⁻¹ y Bᵀ⁻¹` is
  `B⁻¹ yᵀ A⁻¹`, so the product is `A x B B⁻¹ yᵀ A⁻¹ = A (x yᵀ) A⁻¹`. Its trace is
  `trace (x yᵀ)` by `Matrix.trace_mul_comm`.
- `rectangularFourierIntegral_comp_mul_mul`: under the two determinant
  hypotheses, for every function `f` and every `y`,
  `rectangularFourierIntegral ψ ν (fun x => f (A * x * B)) y =
  rectangularFourierIntegral ψ ν f (Aᵀ⁻¹ * y * Bᵀ⁻¹)`. Proof: `X ↦ A X B` is a
  homeomorphism with inverse `X ↦ A⁻¹ X B⁻¹`, hence a measurable embedding.
  `MeasurePreserving.integral_comp` with the previous measure preservation
  rewrites the right side as the integral of
  `f (A x B) * ψ (rectangularPairing (A x B) (Aᵀ⁻¹ y Bᵀ⁻¹))`, and the pairing
  identity finishes. No integrability hypothesis is needed.
- `rectangularFourierIntegral_translate_decomposition`: under the two
  determinant hypotheses, let `Φ` and `Φs l` (for `l` in a finite set `S`) be
  Schwartz–Bruhat functions and `c l` complex numbers. If
  `Φ (A * x * B) = ∑ l ∈ S, c l * Φs l x` for all `x`, then for all `y`,
  `rectangularFourierIntegral ψ ν Φ (Aᵀ⁻¹ * y * Bᵀ⁻¹) =
  ∑ l ∈ S, c l * rectangularFourierIntegral ψ ν (Φs l) y`. Proof: rewrite the
  left side with the previous result, insert the decomposition, and use
  `integral_finsetSum` and `integral_const_mul`. Each term is integrable by
  the published `rectangularFourierIntegrand_integrable`.

## Use

Take `A = k⁻¹` and `B = k'` with `k, k'` in a compact open subgroup `K` of the
general linear group. The first result gives the determinant hypotheses. A
decomposition `Φ (k⁻¹ x k') = ∑ l, χ l (k, k') * Φ l x` then becomes
`Φ̂ (kᵀ y (k'⁻¹)ᵀ) = ∑ l, χ l (k, k') * Φ̂ l y`, with the same coefficients
`χ l (k, k')`. The module `Langlands.Representation.GodementJacquet.TwoBlockDualParabolicIntegral`
packages this for `HarmonicAnalysis.rectangularFourierEquiv` at inverse
transposes.

## Scope

Only matrices of normalized determinant one are treated; for general `A`, `B`
the Haar scaling factor would appear and is not stated here. The results
concern the raw integral `rectangularFourierIntegral` for any `ψ` and `ν`; the
Schwartz–Bruhat Fourier equivalence enters only in the downstream module.
