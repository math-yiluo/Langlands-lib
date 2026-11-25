# The standard Weil operator at the Weyl element

**GKT §2.3.3** (the elements `w_S` of a standard basis, (2.21), p. 61; **Proposition 2.24** and
**(2.24)**, pp. 63–64: the longest Weyl element `w_n` acts by the full Fourier transform), for the
standard Weil operator `r(g)` of `Langlands.Theta.Metaplectic.StandardOperator`.

The module `Langlands.Theta.Metaplectic.WeylElement` defines the longest Weyl element of a
polarization from an identification of the two Lagrangians, and computes `r` at it: the Fourier
transform for the self-dual measure.

## Content

For a pairing `β : X →ₗ[R] Y →ₗ[R] R` and a linear isomorphism `J : Y ≃ X` with
`β(J y, y') = β(J y', y)` (in the book this is a standard basis `e_i ∈ X_B = 0 × Y`,
`e^*_i = J e_i ∈ Y_B = X × 0`):

- `weylIsometry β J hJ`: `w_J (x, y) = (−J y, J⁻¹ x)`, an isometry of `polarizedForm β`
  (`weylIsometry_apply`, `isometryInv_weylIsometry`: `w_J⁻¹ (x, y) = (J y, −J⁻¹ x)`); in the book's
  terms `w(e_i) = −e^*_i`, `w(e^*_i) = e_i`, i.e. `w_n = [[0, I], [−I, 0]]` with `I = J⁻¹`.
- `standardC_weylIsometry`: the c-part of `w_J⁻¹` is `J`, so `ker c = 0`
  (`standardKernel_weylIsometry`).
- `weylForm β J`: the symmetric form `(x, u) ↦ −β(x, J⁻¹ u)` on `X` (`weylForm_symm`).

Over a nonarchimedean local field, `β` perfect, `ψ` continuous and non-trivial:

- `weylBicharacter ψ β J = ψ ∘ weylForm β J`, a self-dual bicharacter
  (`isSelfDualBicharacter_weylBicharacter`).
- `standardIntegrand_weylIsometry`: the integrand of `r(w_J)` at `(x, y)` is
  `ψ(−β(x, y)) φ(J y)`.
- `standardOperator_weylIsometry`: **`r(w_J) φ(x) = ∫_X ψ(−β(x, J⁻¹ u)) φ(u) du`** for the
  self-dual measure of `weylBicharacter ψ β J` (GKT (2.24): `r(w_n) φ(y) = ∫ φ(z) ψ̄(⟨z, I y⟩) dz`,
  with `⟨z, I y⟩ = β(z, J⁻¹ y) = β(y, J⁻¹ z)`). The proof identifies `Y ⧸ ker c = Y ⧸ 0` with `X`
  through `c = J`: `r(w_J)` is a positive multiple of the Fourier transform with the self-dual
  measure, which is unitary (Plancherel, `lintegral_enorm_bicharacterFourier_sq_selfDualMeasure`),
  hence equal to it (`eq_of_eq_smul_of_inner`). In particular the measure `d_w` is the self-dual
  measure carried by `J` (Lemma 2.25).

The partial Weyl elements `w_S`, Lemma 2.25, Proposition 2.26 (multiplicativity on the "Weyl
group") and the block compatibility of §2.3.4 are in `Langlands.Theta.Metaplectic.Block`.

## Declarations

- `weylIsometry`, `weylIsometry_apply`, `isometryInv_weylIsometry`, `standardC_weylIsometry`,
  `standardKernel_weylIsometry`, `weylForm`, `weylForm_apply`, `weylForm_symm`.
- `weylBicharacter`, `isSelfDualBicharacter_weylBicharacter`, `standardIntegrand_weylIsometry`,
  `standardOperator_weylIsometry`.

All in the name space `Langlands.Theta`.

## Dependencies

`Langlands.Theta.Metaplectic.SiegelParabolic` (`eq_of_eq_smul_of_inner`),
`Langlands.HarmonicAnalysis.Bicharacter.SelfDualMeasure` (`selfDualMeasure`, Plancherel).
