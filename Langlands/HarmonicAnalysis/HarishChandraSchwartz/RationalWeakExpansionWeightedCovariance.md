# Covariance of the weighted c-family under unramified self-twists

This module extends the self-twist covariance of `RationalWeakExpansionCCovariance` to the weighted
family `c̃_{P'|P}(s, π ⊗ z) = µ^G(π ⊗ z) µ^{M'}(s(π ⊗ z))⁻¹ c_{P'|P}(s, π ⊗ z)`
(`cWeightedCompactFamily`, module `RationalWeakExpansionCFamily`). The densities are values of the
rational functions `packageDensity` of the two density packages. The module shows that these
functions are invariant under translation by self-twists, that the domain `cWeightedDomain` is
stable under these translations, and that `c̃` is covariant.

## Values of translation-fixed rational functions

For a connected reductive group scheme `S` and a rational function `f` in the function field
`rationalUnramifiedFunctionField` of its unramified characters:

- `rationalValueAt_congr_point` and `exists_rationalValueAt_of_eq` transport regularity and the
  value `rationalValueAt` along an equality of points;
- `exists_rationalValueAt_eq_of_translation_eq`: if translation by `τ`
  (`rationalUnramifiedFunctionFieldTranslation`) fixes `f` and `f` is regular at `τz`, then `f`
  is regular at `z` with the same value. A presentation `f = m/d` at `τz` is translated to a
  presentation `f = (m ∘ τ)/(d ∘ τ)` at `z`;
- `translation_inv_eq_of_translation_eq`: a function fixed by `τ` is fixed by `τ⁻¹`;
- `exists_rationalValueAt_mul_eq_of_translation_eq`: if `τ⁻¹` fixes `f` and `f` is regular at
  `z`, then `f` is regular at `τz` with the same value.

## The package densities

For a density package `P` (`DynamicInducedOrbit.DensityPackage`) of a representation `A`,
`packageDensity_translation_eq` states that translation by an element of the unramified twist
stabilizer of `A` fixes `packageDensity P`. This is `plancherelDensity_stabilizer_fixed` (module
`RationalPlancherelDensity`). `exists_packageDensity_value_mul_eq` and
`exists_packageDensity_value_eq_of_mul_eq` give regularity and equal values at `τz`, resp. at any
`w = τz`.

## The two density parameters

- `standardLeviUnramifiedRestrict_apply` and `standardLeviUnramifiedRestrict_mul` describe the
  restriction of a character of `M_I(F)` to the centralizer of `ζ ∘ i`.
  `standardLeviUnramifiedRestrict_mem_stabilizer` shows that a self-twist `π ≃ π ⊗ τ` restricts to
  a self-twist of the inducing representation of `µ^G`
  (`nonempty_twist_pullback_pullback_iso`).
- `lowerDensityParameter z` is the parameter `sz` of the lower density `µ^{M'}`, read on the
  centralizer scheme of the lower cocharacter `χ_s`. It is the one used in `cWeightedDomain`.
  `lowerDensityParameter_apply` and `lowerDensityParameter_mul` describe it, and
  `lowerDensityParameter_mem_stabilizer` shows that a self-twist of `π` gives a self-twist of the
  inducing representation `sπ` of `µ^{M'}`.

## The weighted family

- `cCompactFamily_selfTwist` restates `cCompactFamily_selfTwist_aux` for an arbitrary vector `Fc`
  of the upper compact picture.
- `cWeightedCompactFamily_apply` unfolds `cWeightedCompactFamily` (by definition).
- `exists_upperDensity_value_mul_eq` and `exists_lowerDensity_value_mul_eq`: for a self-twist
  `π ≃ π ⊗ τ`, the density `µ^G` is regular at `zτ` whenever it is regular at `z`, with the same
  value, and likewise `µ^{M'}` at `s(zτ)` and `sz`.
- `mul_mem_cWeightedDomain_selfTwist`: `cWeightedDomain` is stable under translation by `τ`.
  The nonvanishing of `µ^{M'}` transfers because the values agree.
- `cWeightedCompactFamily_selfTwist`: for `z` and `zτ` in `cWeightedDomain`,
  `c̃(s, π ⊗ zτ)(a · Fc) = (sa) · c̃(s, π ⊗ z)(Fc)` on the fixed compact pictures. The two scalars
  agree by the previous item, and `cCompactFamily_selfTwist` applies to the unweighted family.
  `representationEquiv_smul_apply` moves the scalar through the lower self-twist operator.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), registered as `waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). V.2 (printed p.292) defines
`µ(ω)` for `ω ∈ O`, and Lemma V.2.1 states that `µ` is a regular rational function on `O`. A
function on `O` is invariant under the stabilizer of `ω₀` in `Im X(M)`. Corollary V.2.3 (printed
p.294) concerns the weighted map `ω ↦ µ^G(ω) µ^{M'}(sω)⁻¹ c_{P'|P}(s, ω)` on `O`. The results of
this module say that the Library's weighted family on the parameter cover is compatible with the
identifications along the stabilizer. They are derived from the definitions, from
`plancherelDensity_stabilizer_fixed` and from `cCompactFamily_selfTwist_aux`.
