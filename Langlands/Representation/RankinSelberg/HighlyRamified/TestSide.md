# Model facts for the test representation

Module `Langlands.Representation.RankinSelberg.HighlyRamified.TestSide`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. The step of
Jacquet and Shalika 1985, §4.4 (printed pages 328–330), tests a functional
equation against Whittaker functions `W` of a representation `τ` of `GL_(m+1)`.
It averages `W` over a compact group and twists `τ` by unramified characters.
This module proves the model facts that this test side uses. They hold for a
coefficient model `coefficientModel τ ℓ` of a representation with any nonzero
equivariant functional `ℓ`.

## Provenance

These are standard facts about Whittaker models and smooth representations. Jacquet
and Shalika use them without separate statement. The formal statements and proofs
here are internal to this project.

## Averages

- `algebraicIntegral_mem μ M f hf`: the algebraic integral
  `AlgebraicIntegral.integral μ f` of a simple function whose values lie in a
  submodule `M` lies in `M`. The integral is a finite sum of scalar multiples of
  values of `f`.
- `exists_model_inverseAverage ρ ℓ Φ μG L hΦ w hw hwc` (T-i): let `Φ` be a model
  function that is right invariant under the open subgroup `L`, and let `w` be
  locally constant with compact support. Then the weighted inverse average
  `inverseAverage μG Φ L hΦ w hw hwc`, that is `g ↦ ∫ w(k) Φ(g k⁻¹) dk` (from
  `HighlyRamified.DualAverage`), is again a model function `Ψ`. The average is an
  algebraic integral of the functions `w(k) · (g ↦ Φ(g k⁻¹))`. Each of these is a
  multiple of the model translate `modelRepresentation ρ ℓ k⁻¹ Φ`, so
  `algebraicIntegral_mem` applies to the image of the model in the space of
  functions.

## Levels

- `fixedVectors_ne_bot_of_model ρ ℓ Φ hΦ K hK` (T-ii): let `ρ` be irreducible and
  `Φ ≠ 0` a model function with `Φ(g k) = Φ(g)` for all `k` in a subgroup `K`.
  Then `ρ` has a nonzero `K`-fixed vector. The model map is surjective and, by
  irreducibility (`Representation.IsIrreducible.injective_or_eq_zero`), either
  injective or zero. It is not zero since `Φ ≠ 0`, so the vector `v` with model
  function `Φ` is nonzero. The model functions of `ρ(k) v` and `v` agree, and
  injectivity gives `ρ(k) v = v`.
- `hasPrincipalLevelVector_of_model F τ hτ ℓ Φ hΦ f hK`: the case
  `K = 1 + ϖ^f M_(m+1)(O)` (`Conductor.principalLevelSubgroup F.Carrier m f`) for a
  p-adic field `F`. It gives `HasPrincipalLevelVector F τ f`.

## Central characters

Let `τ` have central character `ω_τ` (`Classification.HasGLCentralCharacter`).

- `model_mul_scalar τ ω hω ℓ Φ z g`: every model function satisfies
  `Φ(g · z I) = ω_τ(z) Φ(g)`.
- `centralCharacter_eq_of_model τ ω hω ℓ Φ hΦ z a hz`: if `Φ ≠ 0` and
  `Φ(g · z I) = a Φ(g)` for all `g`, then `ω_τ(z) = a`. Compare both formulas at a
  point where `Φ` is nonzero.
- `centralCharacter_eq_inv_of_model` (T-iii): if `Φ ≠ 0` and
  `Φ(g · z I) = ω(z)⁻¹ Φ(g)` for every integral unit `z` (`IsIntegralUnit`, from
  `HighlyRamified.DualWeight`), then `ω_τ(z) = ω(z)⁻¹` on the integral units.

## Twists

- `exists_twist_model ψ χ τ ℓ` (T-iv, model transfer): for any character `χ` of
  `Fˣ`, the linear form of an inverse-character functional
  `ℓ : glInverseFunctionals ψ m τ` is also such a functional `ℓ_χ` for the twist
  `τ ⊗ (χ ∘ det)`. The function `g ↦ χ(det g) Φ(g)` lies in the model of the twist
  for each model function `Φ` of `τ`. It uses `twistFunctional` and
  `twistModelLinearMap` from the Library, and the triviality of `χ ∘ det` on the
  upper unipotent group (`determinantCharacter_unipotent`). Since `ℓ_χ` has the
  same linear form, it is nonzero when `ℓ` is.

The remaining statements use a p-adic field `F` with its canonical topological
data `T = F.canonicalTopologicalData`. `ν_y = T.unramifiedCharacter y` is the
unramified character with value `y` at the uniformizer.

- `isIntegralUnit_of_normalizedAbs_eq_one F hx`: an element of normalized absolute
  value `1` is an integral unit. Both `x` and `x⁻¹` have absolute value at most
  `1`, so both are integers.
- `exists_unramified_pow_of_eq_on_units F ω₁ ω₂ h m`: if `ω₁ = ω₂` on the integral
  units, then `ω₁ = ω₂ · ν_y^(m+1)` for some `y : ℂˣ`. The ratio `ω₂⁻¹ ω₁` is
  unramified, so it equals `ν_x` with `x` its value at the uniformizer
  (`eq_unramifiedCharacter`). Take an `(m+1)`-th root `y` of `x` in `ℂ`. Then
  `ν_y^(m+1) = ν_(y^(m+1)) = ν_x`.
- `unramifiedTwist_properties F ψ τ hτ ωτ hωτ hf y` (T-iv): if `τ` is generic for
  `ψ`, has central character `ω_τ` and a principal level vector of level `f`, then
  `τ ⊗ (ν_y ∘ det)` is generic for `ψ`, has a principal level vector of level `f`,
  and has central character `ω_τ · ν_y^(m+1)`. These follow from
  `isGeneric_quasicharacter_twist` (`ν_y` is continuous),
  `hasPrincipalLevelVector_twist_unramified` (`HighlyRamified.InducedLevel`) and
  `hasGLCentralCharacter_twist`.
