# The pro-unipotent radical `I⁺` of the standard Iwahori subgroup

Lean module: `Langlands.Representation.AffineGeneric.Subgroup`, namespace
`Langlands.AffineGeneric`.

Let `F` be a field with a valuative relation, and use the Iwahori order `𝔄` and its radical `𝔓`
from `Langlands.Representation.AffineGeneric.Radical`.

## The subgroup

- `iwahoriRadical m : Subgroup (GeneralLinear (m + 1) F)` is the set of `g` with `g - 1 ∈ 𝔓`
  and `g⁻¹ - 1 ∈ 𝔓`, that is, `I⁺ = 1 + 𝔓`. Closure under products uses
  `gh - 1 = (g - 1) + (h - 1) + (g - 1)(h - 1)`, applied to `g, h` and to `h⁻¹, g⁻¹`. `mem_iwahoriRadical_iff` unfolds membership.
- `conj_mem_iwahoriRadical`: if `ι` and `ι⁻¹` lie in `𝔄`, then `ι I⁺ ι⁻¹ = I⁺`, since
  `ι g ι⁻¹ - 1 = ι (g - 1) ι⁻¹` and `𝔓` is an `𝔄`-ideal.

Over a nonarchimedean local field the subgroup is open and compact.

- `iwahoriRadical_le_maximalCompact`: `I⁺ ≤ GL_{m+1}(𝒪)` (`maximalCompact`).
- `nearIdentity_subset_iwahoriRadical`, `isOpen_iwahoriRadical`: `I⁺` contains the neighbourhood
  `nearIdentity m` of `1` (the `g` such that the entries of `g - 1` and `g⁻¹ - 1` all lie in
  `𝔭`), hence is an open subgroup.
- `isCompact_iwahoriRadical`: `I⁺` is a closed subgroup of the compact group `GL_{m+1}(𝒪)`.

## Group coordinates

For `ϖ : Fˣ`, `groupCoord ϖ g i = aᵢ(g - 1) = coord ϖ (g - 1) i` uses `resOf` on the
weighted matrix entry as in `Radical`. In particular `groupCoord_one` gives zero at `g = 1`.

For a uniformizer `ϖ` (`Iwasawa.IsUniformizingElement`), the coordinates on `I⁺` are the
affine simple coordinates when `m ≥ 1`. For `m = 0` the single coordinate is the principal-unit
homomorphism `g ↦ res(ϖ⁻¹ (g - 1))` from `1 + 𝔭` to the additive group of `k`, with kernel
`1 + 𝔭²`.

- `groupCoord_mul`, `groupCoord_inv`: the map `g ↦ (aᵢ(g - 1))ᵢ` on `I⁺` respects
  multiplication and inversion into the additive group of `k^{m+1}`. The multiplication
  formula uses `coord_add` and `coord_mul_radical`.
- `groupCoord_conj`: for `ι, ι⁻¹ ∈ 𝔄` and `g ∈ I⁺`,
  `aᵢ(ι g ι⁻¹ - 1) = res(ιᵢᵢ) aᵢ(g - 1) res((ι⁻¹)_{ρ i, ρ i})`, by `coord_order_mul`
  and `coord_mul_order`.
