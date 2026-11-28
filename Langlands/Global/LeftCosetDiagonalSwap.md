# Exchanging the variables of a diagonally invariant double integral over `Γ \ H × H`

Module `Langlands.Global.LeftCosetDiagonalSwap`, namespace `Langlands.Global.LeftCosetSpace`.

Let `H` be a topological group and `Γ ≤ H` a subgroup, with the Library's left coset space
`LeftCosetSpace Γ = Γ \ H` and its projection `mk Γ`. A point `ξ` of `Γ \ H` is read at the chosen
representative `Quotient.out ξ ∈ H`.

## Representatives and continuity

- `exists_out_eq`: the representative of the class of `x` is `γ x` for some `γ ∈ Γ`.
- `continuous_out_prod`: if `f : H × H → E` is continuous and invariant under `Γ` acting on the
  left of the first variable, then `(ξ, z) ↦ f(Quotient.out ξ, z)` is continuous on
  `Γ \ H × H`. `continuous_out_prod'` is the same statement for `f : H × Y → E` with any
  topological space `Y` in the second variable. Both hold because `mk Γ × id` is an open quotient
  map and the composite of the function with it is `f`.

## The diagonal exchange

`integral_integral_swap_diagonal`: let `H` be moreover measurable with its Borel structure, locally
compact and Polish, with right invariant Haar measure `dy`, and let `Γ` be discrete, with the
quotient measure `dξ = haarQuotientMeasure Γ hΓ` on `Γ \ H`. Let `Φ : H → H → ℂ` be jointly
continuous and invariant under the diagonal left action, `Φ(γ x, γ y) = Φ(x, y)`, and assume that
`(ξ, z) ↦ Φ(x_ξ, x_ξ z)` (with `x_ξ = Quotient.out ξ`) is integrable for `dξ × dz`. Then

`∫_{Γ \ H} ∫_H Φ(x_ξ, y) dy dξ = ∫_{Γ \ H} ∫_H Φ(x, x_η) dx dη`.

The proof substitutes `y = x_ξ z`, exchanges the order of integration (Fubini), and transports
the integral over `Γ \ H` by the measure preserving right translation by `z`
(`measurePreserving_rightTranslate_haarQuotientMeasure`); the map
`(ξ, z) ↦ (ξ z, z)` of `Γ \ H × H` preserves the product measure (a skew product of
measure preserving maps). It carries the integrand `Φ(x_ξ, x_ξ z)` to `Φ(x_η z⁻¹, x_η)`,
using `exists_out_eq` and the diagonal invariance to compare representatives. Fubini again and
the substitution `x = x_η z⁻¹` (inversion invariance of Haar measure on the unimodular group
`H`) give the right side.

## Provenance

This is the standard unfolding identity for integrals over `Γ \ H × H`, here proved in the
generality needed for the norm-one Levi pairings in `Langlands.Global.AdelicLeviPairingIwasawa`,
where `H` is the norm-one subgroup `M(𝔸)¹` of a Levi factor and `Γ = M(F)`.
