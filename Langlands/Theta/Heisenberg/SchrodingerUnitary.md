# The `L²` inner product of the Schrödinger model

**GKT §1.3.1** (Lemma 1.30 and Theorem 1.31, p. 36: a smooth irreducible representation of the
Heisenberg group is unitarizable), in the Schrödinger model of §1.2.2, where the invariant
Hermitian form is the `L²` inner product of a Haar measure.

The module `Langlands.Theta.Heisenberg.SchrodingerUnitary` defines the `L²` inner product of
Schwartz–Bruhat functions and proves that the Schrödinger representation `schrodingerSB` preserves
it. The metaplectic group of pairs uses it to define `Mp(W)^{ℂ¹}`
(`MetaplecticGroup.unitary ρ (schwartzBruhatInner μ)`, GKT p. 49).

## Content

Let `X` be a topological space with its Borel σ-algebra and `μ` a measure finite on compact sets.

- `integrable_conj_mul_schwartzBruhat`: `conj(f) g` is integrable for Schwartz–Bruhat `f`, `g`
  (continuous with compact support).
- `schwartzBruhatInner μ : SchwartzBruhat X →ₗ⋆[ℂ] SchwartzBruhat X →ₗ[ℂ] ℂ`,
  `(f, g) ↦ ∫ conj(f) g dμ` (`schwartzBruhatInner_apply`), conjugate-linear in `f`;
  `schwartzBruhatInner_self`: `⟨f, f⟩ = ∫⁻ ‖f‖ₑ²` (as a real number).
- `schwartzBruhatInner_map`: a linear map `T` with `∫⁻ ‖T f‖ₑ² = ∫⁻ ‖f‖ₑ²` for all `f` preserves the
  form (polarization: `4 ⟨u, v⟩` is a combination of the four values `⟨u + iᵏ v, u + iᵏ v⟩`).
- `HeisenbergGroup.schrodingerSB_lintegral_enorm_sq`: for a pairing `β`, a continuous character `ψ`
  with `‖ψ t‖ = 1` and a translation-invariant `μ`, the operators of `schrodingerSB` preserve
  `∫⁻ ‖φ‖ₑ²` (the operator of `((x₀, y₀), t)` is a translation by `x₀` times a function of modulus
  one); `HeisenbergGroup.schrodingerSB_inner`: they preserve `schwartzBruhatInner μ`.

## Declarations

- `Langlands.Theta.integrable_conj_mul_schwartzBruhat`, `schwartzBruhatInner`,
  `schwartzBruhatInner_apply`, `schwartzBruhatInner_self`, `schwartzBruhatInner_map`.
- `Langlands.HeisenbergGroup.schrodingerSB_lintegral_enorm_sq`, `schrodingerSB_inner`.

## Dependencies

`Langlands.Theta.Heisenberg.Schrodinger`; Mathlib: `MeasureTheory.Group.Integral`,
`MeasureTheory.Integral.Bochner.ContinuousLinearMap`.
