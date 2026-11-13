# Radicals of parabolics through an intermediate Levi

Lean module: `Langlands.Representation.Intertwining.PQOuterLeviRadicals`.

This module proves the group-theoretic step behind Renard VII.3.5 (iii) (Renard 2026,
French version of 9 July 2026, printed pp.239–240 / PDF pp.245–246): the integration domains of
`J_{P₂|P₁}` and `J_{Q₂|Q₁}` coincide. Renard states `N̄₁ ∩ N₂ = Ū₁ ∩ U₂` without proof; the
proof below is internal.

## Setting

Represented parabolics `P₁ = MN₁`, `P₂ = MN₂` of `G` with the same embedded Levi `M`, an
opposite `P̄₁ = MN̄₁` of `P₁` (`P₁(F) ∩ P̄₁(F) = M(F)`), represented parabolics `Q₁ = LU₁`,
`Q₂ = LU₂` with the same embedded Levi `L`, an opposite `Q̄₁ = LŪ₁` of `Q₁`, with
`P₁(F) ⊂ Q₁(F)`, `P₂(F) ⊂ Q₂(F)`, and a represented parabolic `P' = MN'` of `L` with the same
embedded `M` and `P'(F) = P₁(F) ∩ L(F) = P₂(F) ∩ L(F)`. These are exactly the hypotheses of
`PQIntertwiningOuterLeviStatement`.

## Declaration

- `outerRadical_inf_eq`: `N̄₁(F) ∩ N₂(F) = Ū₁(F) ∩ U₂(F)` as subgroups of `G(F)`.

## Proof

Choose cocharacters `χ`, `ξ`, `ψ` with `P₁ = P(χ)`, `M = Z(χ)`, `Q₁ = P(ξ)`, `L = Z(ξ)`,
`Q₂ = P(ψ)`, `L = Z(ψ)` (`exists_cocharacter_parabolic_levi`). Uniqueness of opposite
parabolics gives `N̄₁(F) = U(χ⁻¹)(F)` and `Ū₁(F) = U(ξ⁻¹)(F)`; also `U₂(F) = U(ψ)(F)`. The
nested decomposition of `P₂ ⊂ Q₂` (`nestedParabolicPointDecomposition`) gives
`U₂(F) ⊂ N₂(F)`. Since `M ⊂ L`, `Z(χ⁻¹) = Z(χ) ⊂ Z(ξ) = Z(ξ⁻¹)`, so the commuting
refinement `θ` of `ξ⁻¹` by `χ⁻¹` exists (`Dynamic.exists_commuting_refinement`), with
`Z(θ) = M`, `U(ξ⁻¹) ⊂ U(θ)`, `U(θ) = (Z(ξ⁻¹) ∩ U(χ⁻¹)) · U(ξ⁻¹)` and
`P(θ) = (Z(ξ⁻¹) ∩ P(χ⁻¹)) · U(ξ⁻¹)` on points. One checks `P(χ)(F) ∩ P(θ)(F) = M(F)`: a point
`a b` of `P(θ)` with `a ∈ Z(ξ⁻¹) ∩ P(χ⁻¹)`, `b ∈ U(ξ⁻¹)` that lies in `P₁ ⊂ Q₁ = P(ξ)` has
`b ∈ U(ξ⁻¹) ∩ P(ξ) = 1`, and then `a ∈ P(χ) ∩ P(χ⁻¹) = M`. Uniqueness of the opposite
parabolic (`oppositeDynamicParabolicUniqueness`) then gives `U(θ) = U(χ⁻¹)`.

- `⊂`: write `x ∈ N̄₁ ∩ N₂ = U(θ) ∩ N₂` as `y u` with `y ∈ L ∩ U(χ⁻¹)`, `u ∈ U(ξ⁻¹)`. Since
  `y ∈ L ⊂ P(ψ)` and `x ∈ P₂ ⊂ Q₂ = P(ψ)`, `u ∈ U(ξ⁻¹) ∩ P(ψ) = U(ξ⁻¹) ∩ U(ψ)`
  (`unipotent_inf_parabolic_eq_unipotent_inf_unipotent`, as `Z(ψ) = Z(ξ⁻¹)`), so
  `u ∈ U₂ ⊂ N₂`. Hence `y = x u⁻¹ ∈ N₂ ∩ L ⊂ P₂ ∩ L = P' = P₁ ∩ L ⊂ P(χ)`, and
  `y ∈ U(χ⁻¹) ∩ P(χ)` forces `y = 1`. So `x = u ∈ Ū₁ ∩ U₂`.
- `⊃`: `Ū₁ = U(ξ⁻¹) ⊂ U(θ) = N̄₁` and `U₂ ⊂ N₂`.

The private helper `range_comp_le'` records that the range of a composite lies in the range of
its second factor.
