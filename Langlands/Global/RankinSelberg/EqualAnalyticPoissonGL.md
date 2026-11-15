# Poisson summation twisted by `GL_n(𝔸)`

Module `Langlands.Global.RankinSelberg.EqualAnalyticPoissonGL`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

Main result `hasSum_poisson_mul`: for a standard `ψ`, `Φ ∈ schwartzBruhat F n` and
`g ∈ GL_n(𝔸)`, the family `η ↦ |det g|⁻¹ Φ̂(η ᵗg⁻¹)` over `η ∈ F^n` has sum
`Σ'_{ξ ∈ F^n} Φ(ξ g)`. This is the form of Poisson summation used for theta series and
Eisenstein series (Cogdell 2004, §2.3, p.209), with `ᵗg⁻¹ =
GeneralLinear.inverseTranspose n (Adeles F) g`.

## Provenance

Internal. It combines `hasSum_fourierTransform_ratRow` and the change of variables
`integral_comp_rightMul`.

## Declarations

- `archimedeanCoordinates_mul`, `finiteCoordinates_mul`: coordinates of `x M`.
- `exists_norm_archimedeanCoordinates_mul_le`: `‖(x M)_∞‖ ≤ c ‖x_∞‖`.
- `IsRowDominated.comp_mul`: if `Φ` is dominated, so is `x ↦ Φ(x g)`. Write `x = (x g) g⁻¹`; clear
  the finite denominators of `g⁻¹` and bound `‖x_∞‖` by `‖(x g)_∞‖`.
- `rowPairing_mul`: `⟨x M, y⟩ = ⟨x, y ᵗM⟩`.
- `inverseTranspose_val`: the matrix of `GeneralLinear.inverseTranspose n (Adeles F) g` is
  `ᵗ(g⁻¹)`.
- `fourierTransform_comp_mul`: the transform of `x ↦ Φ(x g)` at `y` is `|det g|⁻¹ Φ̂(y ᵗg⁻¹)`.
- `hasSum_poisson_mul`.
