# Additive orthogonality, coset Fourier integrals and dilation

This helper module is internal infrastructure for the proof of
`Langlands.GodementJacquet.LocalTateConductorStatement`. It computes actual
plus-sign Fourier integrals
`fourierIntegral ψ ν Φ y = ∫ ψ(x y) Φ(x) dν(x)` for the test functions that the
proof needs. It holds over an arbitrary nonarchimedean local field.

## Character facts

Assume `ψ` satisfies `HasIntegerConductor ψ`: it is trivial on `O`, and any
`y` with `ψ(z y) = 1` for every `z ∈ O` lies in `O`.

- `char_eq_one_of_mem_ball_zero`: `ψ = 1` on `O = ball 0`.
- `exists_char_ne_one`: if `y ∉ ϖ^{-n} O`, some `t ∈ ϖ^n O` has
  `ψ(t y) ≠ 1`. Suppose not. Then `ψ(z · ϖ^n y) = 1` for all `z ∈ O`, so the
  second conductor clause puts `ϖ^n y` in `O`, a contradiction.

## Orthogonality and coset transforms

`integral_ball_char` proves, for any additive Haar measure `ν`,

`∫_{ϖ^n O} ψ(x y) dν(x) = ν(ϖ^n O)` if `y ∈ ϖ^{-n} O`, and `0` otherwise.

In the first case the integrand is identically one. In the second case, take
`t` from `exists_char_ne_one`. Translation invariance of `ν` under `x ↦ x + t`
gives `I = ψ(t y) I`, so `I = 0`.

`fourierIntegral_cosetIndicator` then evaluates the transform of the coset
indicator `1_{x0 + ϖ^n O}`. Translating by `x0` gives

`ψ(x0 y) · (ν(ϖ^n O) if y ∈ ϖ^{-n} O, else 0)`.

## Dilation

`dilate b Φ = Φ(b ·)` for `b ∈ Fˣ`. It is a complex-linear map of
Schwartz--Bruhat functions: local constancy is preserved by composition with a
continuous map, and compact support by `HasCompactSupport.comp_smul`.
`fourierIntegral_dilate` proves

`F(dilate b Φ)(y) = abv(b)⁻¹ · FΦ(b⁻¹ y)`.

The proof pushes `ν` forward along the measurable embedding `x ↦ b x`. The
published `HarmonicAnalysis.generalScalarHaarScalingStatement` identifies the
image measure as `abv(b)⁻¹ ν`, and `integral_smul_nnreal_measure` extracts the
scalar.

## Provenance

These are standard local computations of the kind used in Tate's thesis
(source `tate-1967-thesis`). Here they are internal derived lemmas, not
translations of numbered statements. The sources for the target itself are
listed in `LocalTateConductorStatement.md`.
