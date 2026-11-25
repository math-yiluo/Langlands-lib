# The constant term along `P_J` on the threshold region, uniformly in the representation

Module `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTermRegionComparison`,
namespace `Langlands.HarishChandraSchwartz`. Helper module of the proof of
`RationalOrbitConstantTermThresholdStatement`.

## Purpose

The region theorem of `RationalMinimalLeviDimensionThreshold` is stated for the stable
pairings of the I.4.1 data built from the simultaneous basis and its split components `A J`.
The target uses the published constant term `standardConstantTerm hA'` (Waldspurger's
Proposition I.6.2, printed p. 249) for an **arbitrary** compatible split component `A'` of `M_J`.
This module identifies the two by the uniqueness of right-finite constant terms, and packages
the result for finite sums of coefficients.

## Statements

- `characterOrder_componentCharacterRestriction`: the order of `α|_A` at `x ∈ A(F)` is the order
  of `α` at the image of `x` in `S(F)` (`Plancherel.rationalCharacterValuation_characterRestrict`).
- `mem_thresholdRegion_of_mem_standardCone`: for a compatible split component `A'` of `M_J`
  and `t ≥ 0`, the image in `M_0(F)` of every point of the source's cone
  `standardCone i ν J q' (q^{-t})` lies in `rationalConstantTermThresholdRegion J t`. Outside `J`
  this is `characterNorm_eq_rpow` with `eval_rationalComponentH0`; for `α ∈ J` the restriction
  `α|_{A'}` is `0` because it pairs to zero with every cocharacter
  (`IsCompatibleStandardSplitComponent.latticePairing_eq_zero`) and the lattice pairing of the
  split torus `A'` is perfect (`CocharacterUniformizer.latticePairing_isPerfPair`).
- `isStandardConstantTerm_coefficientConstantTerm_of_region`: for an admissible `ρ`, a stable
  pairing `b` of the I.4.1 data of `P_J` (simultaneous data) and any `ℓ`, `v`, the Library's
  constant term `coefficientConstantTerm` (`m ↦ b(ǰ(ℓ), J_δ(m) j(v))`, `δ = δ_{U_J}`) is a
  constant term of `x ↦ ℓ(ρ(x) v)` for `A'` in the sense of `IsStandardConstantTerm`. For
  `m' ∈ M_J(F)`, apply the region theorem to `v` and `ρ̃(m'⁻¹) ℓ`; the cone of `A'` lies in the
  region; `IsStablePairing.map_action` moves `m'` back; and
  `StablePairingData.inv_sqrt_mul_eq_coefficientConstantTerm` concludes.
- `isRightFinite_coefficientConstantTerm_standard`: that constant term is right finite for the
  image of `A'(F)` (`IsStablePairing.exists_admissible_coefficientConstantTerm` with
  `hasIwahoriContractionBasis_standard`, and `isRightFinite_of_mem_coefficientFunctionSpace`).
- `pairing_eq_sqrt_mul_coefficientConstantTerm`,
  `pairing_eq_standardHalfModulus_mul_coefficientConstantTerm`: `b(ǰ(ℓ), j(ρ(m) v))` is
  `δ_{U_J}(m)^{1/2}` times the constant term at `m`, for `m ∈ M_J(F)`, resp. at
  `minimalLeviInclusion m` for `m ∈ M_0(F)` (`apply_mk_eq_sqrt_mul_normalized`).
- `exists_constantTerm_data_of_region`: the three properties above for one coefficient.
- `exists_constantTerm_dimension_threshold` (main statement): for `J ⊆ Δ`, a compatible split
  component `A'` of `M_J` with a standard cocharacter `ζ'` of `J`, and a basis member `K₁ ∈ B`,
  there is `K₂ ∈ B`, `K₂ ≤ K₁`, such that for every `d` there is `t > 0` with
  `f(m) = standardHalfModulus (minimalLeviInclusion m) · standardConstantTerm hA' f
  (minimalLeviInclusion m)` for every admissible `ρ` (universe `uV`) with
  `finrank (fixedVectors ρ K₂) ≤ d`, every `f` in the span of the coefficients
  `x ↦ ℓ(ρ(x) v)` with `v`, `ℓ` fixed by `K₁`, and every
  `m ∈ rationalConstantTermThresholdRegion J t`. Proof: fix a stable pairing
  (`exists_isStablePairing`); by span induction every such `f` has a right-finite constant term
  `φ` for `A'` with `f = δ^{1/2} φ` on the region; `standardConstantTerm_eq` identifies `φ`.

## Note on kernel checking

The kernel times out when it must identify `↑(minimalLeviInclusion m)` with `↑m` inside the
pairing identity by definitional unfolding; the proof rewrites with `coe_minimalLeviInclusion`
instead.

## Check

Development check: 0 errors, 0 warnings.
