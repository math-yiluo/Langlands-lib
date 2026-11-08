# The test data of the adjacent-rank step

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. Concrete choices and
elementary facts for the test data of Jacquet–Shalika 1985, §4.4, conditions (6)–(8) (printed
page 328) and (4.4.18) (printed page 330), and for the internal test vector `f'` that
replaces their `W'` of (4.4.16)–(4.4.17).

## Characters and weights

- `TrivialOnPrincipalUnits.mul`, `.pow`: triviality on `1 + 𝔭^b` is preserved by products and
  powers of characters.
- `unitCharWeight μ t = μ(t)` for integral units `t`, and `0` otherwise. This is
  `S₁ = μ · 1_(O^×)` of condition (6). `invCharWeight μ t = μ(t)⁻¹` for `t ≠ 0`.
- `isIntegralUnit_add_iff`, `unitCharWeight_add`: for `b ≥ 1` and `d ∈ 𝔭^b`, `x + d` is an
  integral unit iff `x` is. If `μ` is trivial on `1 + 𝔭^b`, then `S₁(x + d) = S₁(x)`
  (`omega_eq_of_sub_mem`, DualTarget). This is the periodicity required by
  `exists_unit_inversion` (UnitInversion).
- `inPow_pow_mul`: `ϖ^c o ∈ 𝔭^c` for `ϖ ∈ 𝔭` and integral `o`.
- `integralFourier ψ T Φ₂ v = Σ_z Φ₂(z) ψ(⟨z, v⟩)` for integral `v`, and `0` otherwise: the
  function `S₂` of the dual reduction. `finiteFourier_product_eq`: if
  `Σ_(u ∈ T₁) Φ₁(u) ψ(u ξ) = S₁(ξ)` on `O`, the finite Fourier transform of `Φ₁ ⊗ Φ₂` over
  `T₁ × T₂` is `S₁(ξ₀) S₂(ξ_tail)` on integral `ξ` (`finiteFourier_product`, TestData).

## The last coordinate

- `lowerTriangular_entry_ne_zero`, `determinant_lowerTriangular_eq`: for `c ∈ GL_1`, `c₀₀ ≠ 0`
  and `det c = c₀₀` as units.
- `lastWeight_unitCharWeight`: with `S₁ = (μ χ) 1_(O^×)` and `η = μ⁻¹`, the last-coordinate weight
  `S₁(c) χ(c)⁻¹ η(c)` of DualReduction is the indicator of the integral units. This is the
  hypothesis `hκ` of `dual_integral_reduction`, and it fixes `S₁` once the equivariance
  character `μ = ω_σ χ^(m+1)` of `f'` is fixed.
- `lowerBlockPair_diag_one`, `lowerBlockPair_diag_inv`, `lowerBlockPair_diag_symm`,
  `inverseTranspose_lowerBlockPair_diag`: for `d = diag(I, c)` (published `lowerBlockPair 1 0 c`),
  `d⁻¹ = diag(I, c⁻¹)`, `d` is symmetric, and so its inverse transpose is `diag(I, c⁻¹)`.
- `secondDual_lowerBlockPair`: if `f'(g diag(I, c)) = μ(c) f'(g)` for integral units `c`, then
  `f̃'(y diag(I, c)) = μ(c)⁻¹ f̃'(y)`. Here `f̃'(y) = f'(w ᵗy⁻¹)` (published
  `secondDualFunction_apply`) and the inverse transpose of `y diag(I, c)` is
  `ᵗy⁻¹ diag(I, c⁻¹)`. This is the hypothesis `hη` of `dual_integral_reduction` with
  `η = invCharWeight μ`.

## Canonical facts

- `inPow_one_of_ord_eq_one`: an element of order `1` lies in the maximal ideal. Its normalized
  absolute value is `q⁻¹ ≤ 1`, and its inverse, of absolute value `q`, is not integral.
- `trivialOnPrincipalUnits_of_conductor_le`: a quasicharacter with conductor exponent
  `a(χ) ≤ n`, `n ≥ 1`, is trivial on `1 + 𝔭^n`. The `1 × 1` matrix `(u)` lies in the principal
  congruence subgroup of level `n` (published `exists_mem_principalLevelSubgroup`). Its
  determinant `u` therefore lies in the published principal units of level `n`
  (`determinant_mem_principalUnits`, InducedLevel), where `χ` is trivial by
  `multiplicativeTrivialAt_iff_conductor_le`.
