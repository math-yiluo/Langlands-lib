# Fourier support of a twisted indicator function on matrices

## Setting

`K` is a field with a topology, a measurable structure and measurable addition; `ψ` is a Library
`UnitaryAdditiveCharacter K` (with complex values `ψ.complex`) and `ν` a Library
`AdditiveHaarMeasure K` that is σ-finite. Matrices carry the product measure
`RankinSelberg.rectangularMeasure ν r s`, and the Library Fourier integral is
`rectangularFourierIntegral ψ ν Φ x = ∫ Φ(y) ψ(⟨y, x⟩) dy` with the entry pairing
`⟨y, x⟩ = ∑_{i,j} y_{ij} x_{ij}` (`rectangularPairing`).

## Declarations

- `rectangularPairing_add_left`: the entry pairing is additive in its first argument.
- `rectangularFourierIntegral_eq_zero_of_add_left`: if `Φ(z + y) = c Φ(y)` for all `y` and
  `c ψ(⟨z, x⟩) ≠ 1`, then the Fourier integral of `Φ` vanishes at `x`.
- `twistedIndicator ψ P b'` (definition): for an additive subgroup `P` of the `N × N` matrices and a
  matrix `b'`, the function `y ↦ ψ(-tr(b' (y - 1)))` if `y - 1 ∈ P`, and `0` otherwise.
  The lemmas `twistedIndicator_apply_of_mem` and `twistedIndicator_apply_of_not_mem` give its values.
- `twistedIndicator_add_left`: for `z ∈ P`, `Φ(z + y) = ψ(-tr(b' z)) Φ(y)`.
- `rectangularPairing_eq_trace`: for square matrices, `⟨z, x⟩ = tr(z xᵀ)`.
- `trace_mul_sub_eq_one_of_rectangularFourierIntegral_ne_zero`: if the Fourier integral of
  `twistedIndicator ψ P b'` is nonzero at `x`, then `ψ(tr(z (xᵀ - b'))) = 1` for every `z ∈ P`.
- `rectangularFourierIntegral_twistedIndicator_of_trace_eq_one`: if `P` is a measurable set and
  `ψ(tr(z (xᵀ - b'))) = 1` for all `z ∈ P`, the Fourier integral of `twistedIndicator ψ P b'` at
  `x` equals `μ.real P · ψ(tr x)`, where `μ = RankinSelberg.rectangularMeasure ν N N` and
  `μ.real P = (μ P).toReal`. This is the Haar volume of `P` when `μ P` is finite, and `0` when
  `μ P = ∞`.
- `LatticeChain.matrixFiltration 𝓛 k` (definition): for a nonarchimedean local field `K` and a
  lattice chain `𝓛` in `K^N`, the additive subgroup of matrices `y` with `Matrix.toLin' y ∈ 𝔓^k(𝓛)`
  (`LatticeChain.endFiltration`). `mem_matrixFiltration` unfolds membership.
- `LatticeChain.toLin'_mem_endFiltration_of_rectangularFourierIntegral_ne_zero`: let `c ≠ 0` with
  `ψ(c a) ≠ 1` for some `a ∈ 𝔬_K`. If the Fourier integral of
  `twistedIndicator ψ (𝓛.matrixFiltration k) b'` is nonzero at `x`, then
  `Matrix.toLin' (c⁻¹ (xᵀ - b')) ∈ 𝔓^{1-k}(𝓛)`.

In the intended use, `ψ = ψ₀` has conductor `𝔬_K` and `c = ϖ⁻¹`, so `ψ₀(c ·)` is trivial on `𝔭_K`
but not on `𝔬_K`; the conclusion is `ϖ (xᵀ - b') ∈ 𝔓^{1-k}(𝓛)`. With `b' = ϖ⁻¹ b` this is
`ϖ xᵀ - b ∈ 𝔓^{1-k}(𝓛)`, the support bound used in `ConductorUpperBound`.

## Provenance

This internal step of T2 proves the support inclusion for the Fourier transform of a
character-twisted lattice indicator directly from translation invariance. The last step uses the trace duality
`LatticeChain.mem_endFiltration_one_sub_of_forall` of the module `TraceDuality`
(Bushnell–Kutzko (1993), (1.1.4)).

## Proof

For `rectangularFourierIntegral_eq_zero_of_add_left`: `rectangularMeasure` is a product of Haar
measures, hence left-invariant under addition (`Measure.pi` instance), so
`integral_add_left_eq_self` gives `Φ̂(x) = ∫ Φ(z + y) ψ(⟨z + y, x⟩) dy`. By the hypothesis on `Φ`
and additivity of the pairing, the integrand is `c ψ(⟨z, x⟩) Φ(y) ψ(⟨y, x⟩)`, so
`Φ̂(x) = c ψ(⟨z, x⟩) Φ̂(x)` and `(1 - c ψ(⟨z, x⟩)) Φ̂(x) = 0`. No integrability is needed (both
sides are Bochner integrals, possibly zero).

`twistedIndicator_add_left` splits on `y - 1 ∈ P`; since `z ∈ P`, `z + y - 1 ∈ P` exactly when
`y - 1 ∈ P`, and on `P + 1` the character value factors as `ψ(-tr(b' z)) ψ(-tr(b'(y - 1)))`.

For the Fourier support, if `ψ(tr(z (xᵀ - b'))) ≠ 1` for some `z ∈ P`, then
`ψ(-tr(b' z)) ψ(⟨z, x⟩) = ψ(tr(z xᵀ) - tr(z b')) ≠ 1` and the first lemma forces `Φ̂(x) = 0`.

For the value where the phase is trivial, substitute `y = 1 + z` using translation
invariance. The integrand on `P` is `ψ(tr x)` because
`ψ(-tr(b' z)) ψ(tr(z xᵀ)) = 1`, and it vanishes outside `P`. Since `P` is measurable,
`integral_indicator_const` gives the integral of the constant times the indicator as
`μ.real P · ψ(tr x)`.

For the lattice form, apply `mem_endFiltration_one_sub_of_forall` to `y = toLin'(c⁻¹ (xᵀ - b'))`
and the character `t ↦ ψ(c t)`. For `z ∈ 𝔓^k(𝓛)`, its matrix `Z` lies in `matrixFiltration 𝓛 k`
and `tr(y z) = c⁻¹ tr((xᵀ - b') Z)`, so `ψ(c tr(y z)) = ψ(tr(Z (xᵀ - b'))) = 1`.
