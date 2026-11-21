# Intertwining of representations of subgroups

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), §4.1, printed p. 144 (PDF p. 156), and (5.1.7), printed p. 160 (PDF p. 172). This is definition 1 of Task 7427.

Representations are Mathlib's `Representation ℂ K W`: group homomorphisms from a subgroup `K` to `W →ₗ[ℂ] W`, for any complex vector space `W`. The definitions in this module make sense for subgroups of any group `G` and for any representations. Smoothness and finite dimensionality, which BK93 assumes for representations of compact open subgroups of `Aut_F(V)`, are imposed by the predicates that use these definitions (`IsHeisenbergRepresentation`, `IsBetaExtension`, the statements of Task 7427).

## Definitions

- `intertwiningDomain K₁ K₂ x` is the subgroup `x⁻¹K₁x ∩ K₂`. It is written as the set of `h ∈ K₂` with `x h x⁻¹ ∈ K₁` (`mem_intertwiningDomain`).
- `intertwiningDomainConj K₁ K₂ x : x⁻¹K₁x ∩ K₂ →* K₁` is `h ↦ x h x⁻¹`, and `intertwiningDomainIncl K₁ K₂ x` is the inclusion into `K₂`.
- For representations `ρ₁` of `K₁` and `ρ₂` of `K₂`, `intertwiningSpace ρ₁ ρ₂ x` is the `ℂ`-space `I_x(ρ₁, ρ₂)` of `x⁻¹K₁x ∩ K₂`-homomorphisms from `ρ₁^x : h ↦ ρ₁(x h x⁻¹)` (that is, `ρ₁ ∘ intertwiningDomainConj`) to the restriction of `ρ₂` (`ρ₂ ∘ intertwiningDomainIncl`). It is Mathlib's `Representation.IntertwiningMap`, a `ℂ`-module.
- `Intertwines ρ₁ ρ₂ x` says that `I_x(ρ₁, ρ₂)` contains a nonzero element. `representationIntertwining ρ₁ ρ₂` is the set `I_G(ρ₁, ρ₂)` of such `x`, and `representationSelfIntertwining ρ = I_G(ρ, ρ)`. For self-intertwining, `intertwiningSpace ρ ρ x` is `I_x(ρ)`.
- `characterRepresentation χ` is the one-dimensional representation `h ↦ χ(h) · id` of `H` on `ℂ` attached to a character `χ : H →* ℂˣ`.

## Direction of the homomorphisms

This module uses the convention of the task contract: `I_x(ρ₁, ρ₂) = Hom_{x⁻¹K₁x ∩ K₂}(ρ₁^x, ρ₂)` with `ρ₁^x(h) = ρ₁(x h x⁻¹)`. BK93 (5.1.7) writes `I_g(ρ) = Hom_{K^g ∩ K}(ρ, ρ^g)` with the same `ρ^g` on `K^g = g⁻¹Kg`, so its homomorphisms go the other way. BK93 §4.1 (p. 144) phrases intertwining with `^gρ(y) = ρ(g⁻¹ y g)` on `gKg⁻¹`, so `ρ^x = ^{x⁻¹}ρ`, and `x` intertwines `ρ` in the sense of this module exactly when `x⁻¹` intertwines `ρ` in the sense of §4.1. For finite-dimensional representations of compact groups, the two directions give spaces of equal dimension (complete reducibility), so the same sets `I_G(ρ)` arise. This module proves no comparison between the two directions; it fixes the contract's direction.

## Agreement with intertwining of characters

`mem_representationIntertwining_characterRepresentation_iff` proves that for characters `χ₁` of `H₁` and `χ₂` of `H₂`, `x ∈ representationIntertwining (characterRepresentation χ₁) (characterRepresentation χ₂)` exactly when `x ∈ characterIntertwining χ₁ χ₂` (Task 7422, definition 3, `Langlands.BushnellKutzko.characterIntertwining`). A nonzero `ℂ`-linear map `ℂ → ℂ` is multiplication by a nonzero scalar, so it intertwines `χ₁^x` with `χ₂` exactly when `χ₁(x h x⁻¹) = χ₂(h)` on `x⁻¹H₁x ∩ H₂`.
