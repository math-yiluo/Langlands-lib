# Fourier analysis for a symmetric nondegenerate pairing on a real vector space

Module `Langlands.Global.RankinSelberg.SchwartzBruhatProof.ArchFourier`, namespace
`Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof`. It is a supporting module for
the proof of `Langlands.Global.RankinSelbergGlobal.SchwartzBruhatStatement`. It supplies the
archimedean half of the Fourier inversion argument, in a generic form that does not mention
number fields.

## Provenance

These are internal lemmas. They reduce the Fourier transform for an arbitrary symmetric
nondegenerate pairing to Mathlib's Fourier transform on a Euclidean space, which maps Schwartz
functions to Schwartz functions (`SchwartzMap` Fourier transform) and satisfies Fourier
inversion (`Continuous.fourierInv_fourier_eq`). This is the archimedean input of Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Lemma C.3.1 and (C.6), printed p.554.
The inversion constant is not computed here. It is pinned down globally in module `Fourier`.

## Setting

`W` is a finite-dimensional real normed space with Borel measurable structure, `μ` an additive
Haar measure on `W`, and `B : W →ₗ W →ₗ ℝ` a bilinear form.
`E` is a finite-dimensional real inner product space.

## Declarations

- `pairingFourier μ B φ ξ = ∫ φ(w) 𝐞(B(w, ξ)) dμ(w)`, where `𝐞(t) = exp(2πit)` is Mathlib's
  `Real.fourierChar`.
- `exists_map_eq_smul_volume`: for a continuous linear isomorphism `P : W ≃L E`, the image
  `μ.map P` is `c • volume` with `c ≠ 0`. This is uniqueness of Haar measure
  (`Measure.isAddLeftInvariant_eq_smul`); `c ≠ 0` because `μ.map P` gives positive mass to
  `univ`.
- `exists_inner_eq`: if `B` has trivial right kernel, then for every `P` there is a linear
  isomorphism `Q : W ≃L E` with `B(w, ξ) = ⟪P w, Q ξ⟫`. Take
  `Q ξ = Σ_i B(P⁻¹ b_i, ξ) b_i` for an orthonormal basis `(b_i)` of `E`. It is injective by
  nondegeneracy, and bijective by equality of dimensions.
- `pairingFourier_eq`: if `B(w, ξ) = ⟪P w, Q ξ⟫` and `μ.map P = c • volume`, then
  `F_B φ(ξ) = c · 𝓕⁻(φ ∘ P⁻¹)(Q ξ)`. This is the change of variables `y = P w`.
- `integrable_of_comp`: integrability transfers from `f ∘ e` on `(W, μ)` to `f` on
  `(E, volume)`.
- `pairingFourier_pairingFourier`: assume `B` symmetric with `B(w, ξ) = ⟪P w, Q ξ⟫`, and
  `μ.map P = c_P • volume`, `μ.map Q = c_Q • volume` with `c_P, c_Q ≠ 0`. Then
  `F_B F_B φ(x) = c_P c_Q φ(-x)` for continuous integrable `φ` with integrable `F_B φ`.
  By symmetry also `B(w, ξ) = ⟪Q w, P ξ⟫`. So `F_B φ = c_Q 𝓕⁻ g ∘ P` with `g = φ ∘ Q⁻¹`, and
  `F_B F_B φ = c_P c_Q 𝓕⁻ 𝓕⁻ g ∘ Q`. Finally `𝓕⁻ 𝓕⁻ g = g(-·)` by Mathlib's inversion theorem
  applied to `g(-·)` (`Real.fourierInv_eq_fourier_comp_neg`). No determinant is computed.
- `exists_schwartz_pairingFourier`: `F_B φ` is a Schwartz function for Schwartz `φ`. It is
  `c_Q · (𝓕⁻(φ ∘ Q⁻¹)) ∘ P`, built from `SchwartzMap.compCLMOfContinuousLinearEquiv` and the
  Schwartz-space inverse Fourier transform.
- `exists_pairingFourier_inversion` (main result): for symmetric `B` with trivial kernel, there
  is one constant `C : ℂ` such that every Schwartz `φ` has a Schwartz transform `F_B φ` and
  `F_B F_B φ(x) = C φ(-x)`. Here `P` is any isomorphism with
  `EuclideanSpace ℝ (Fin (finrank ℝ W))` (`ContinuousLinearEquiv.ofFinrankEq`), `Q` comes from
  `exists_inner_eq`, and `C = c_P c_Q`.
