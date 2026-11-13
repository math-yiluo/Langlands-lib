# Unramified twists of gamma factors over every nonarchimedean local field

Module `Langlands.Representation.RankinSelberg.LocalFieldUnramifiedTestTwist`.

## Setting

`F` is a nonarchimedean local field
(`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`)
of any characteristic. `ϖ : Fˣ` is a uniformizer
(`hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ`), and `q` is a natural number
with `hq : 1 < q`. `abv : AbsoluteValue F ℝ` is normalized by
`habv : abv ϖ = q⁻¹` and `hunit : abv x = 1` whenever `x` has valuation `1`. These are the
fields `uniformizer`, `abv_uniformizer` and `abv_unit` of `Conductor.IsJacquetNormalization`,
plus `1 < q`, which follows from its field `residueCardinality`. The results do not need
`q` to be the residue cardinality.

For `z : ℂˣ`, `χ_z = Conductor.UnramifiedPrincipalSeries.character hϖ z` is the published
unramified character `a ↦ z ^ ord(a)` of `Fˣ`, so `χ_z(ϖ) = z` and `χ_z` is trivial on
units. `rationalRescale z` is the published substitution `G(X) ↦ G(zX)` on
`RationalFunctions` (`X = q^(-s)`).

## Definition

`unramifiedDetTwist hϖ z σ` is the twist `σ ⊗ (χ_z ∘ det)` of a representation `σ` of
`GL_m(F)`, that is, `Langlands.twist ((character hϖ z).comp determinant) σ`. It is a
name for the twisted representation in the statements below and adds no new
construction.

## Results

- `abv_eq_inv_zpow_ord hϖ habv hunit a`: for `a : Fˣ`,
  `abv a = (q⁻¹) ^ ord(a)`, with `ord = Conductor.UnramifiedPrincipalSeries.ord hϖ`.
  Proof: `a ϖ^(-ord a)` has valuation `1` (by `valuation_eq_pow_ord`), so its absolute
  value is `1`. Multiplicativity of `abv` then gives the formula; `q⁻¹ ≠ 0` because
  `q⁻¹ = abv ϖ` and `ϖ ≠ 0`.
- `unramifiedCharacter_eq_abv_cpow hq hϖ habv hunit hu a`: if
  `spectralShiftUnit q hq u = z` (that is, `q^(-u) = z`), then `χ_z(a) = abv(a) ^ u`
  (complex power). Proof: both sides equal `q^(-u · ord a)`. The left side is
  `(q^(-u))^(ord a)`, rewritten by `Complex.cpow_int_mul`. The right side is
  `((q⁻¹)^(ord a))^u = (q^(-ord a))^u` (by `inv_zpow'`), rewritten with `Complex.ofReal_cpow` and `Complex.cpow_mul`, whose
  argument side conditions hold because `log q` is real.
- `isGeneralPairGammaFactor_unramifiedTwist hq hϖ habv hunit z π σ h`: if
  `IsGeneralPairGammaFactor q ψ abv ν π σ G`, for `π` of `GL_(r+1)(F)` and `σ` of
  `GL_(n+1)(F)`, then `rationalRescale z G` is the gamma factor of both
  `(π, unramifiedDetTwist hϖ z σ)` and `(unramifiedDetTwist hϖ z π, σ)`. Proof: choose
  `u` with `spectralShiftUnit q hq u = z` (`HighlyRamified.exists_spectralShiftUnit_eq`),
  so `χ_z = |·|^u` by the previous lemma. Apply the published field-generic transport
  `UnramifiedGammaTwist.pair_both` with the Borel σ-algebras, which is the measurable
  structure in `IsGeneralPairGammaFactor`.
- `isGeneralSymmetricGammaFactor_unramifiedTwist`: the same for the larger-rank-first
  relation `IsGeneralSymmetricGammaFactor`. Proof: case split on its `if` and apply the
  pair result to `(π, σ)` or to `(σ, π)`.
- `isGeneralSymmetricGammaFactor_unramifiedTest hq hϖ habv hunit z π h` and
  `isGeneralPairGammaFactor_unramifiedTest`: if `G` is the gamma factor of
  `(π, rankOneCharacter 1)`, then `rationalRescale z G` is the gamma factor of
  `(π, rankOneCharacter χ_z)`, for the symmetric and the pair relations respectively.
  Proof: the twist of the trivial rank-one character by `χ_z ∘ det` is
  `rankOneCharacter χ_z` (`HighlyRamified.twist_rankOneCharacter_one`).

## Provenance

Internal supporting results. Mathematically, twisting by `|det|^u` replaces `s` by
`s + u` in the Rankin–Selberg integrals, so the gamma factor `γ(s, π × σ ⊗ χ, ψ)`
becomes `γ(s + u, π × σ, ψ)` when `χ = |·|^u` (Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg convolutions*, 1983). The Library proves this transport for every field
as `UnramifiedGammaTwist.pair_both`, and over `PadicField` as `padic_pair_both`. This
module only identifies the unramified character `χ_z` with `|·|^u` over an arbitrary
nonarchimedean local field and restates the transport for the general-field relations
of `RankinSelberg/GeneralPairGamma`. It is used for the rank-one gamma factors
`γ(s, π × χ_{z_i}, ψ)` in the corank-one spherical functional equation (Task 5680).
