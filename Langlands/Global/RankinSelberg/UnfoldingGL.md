# General linear facts for the unfolding

Internal helper module for `UnequalUnfoldingReduction.md`.
Provenance: internal.

## Padding `diag(g, I)`

- `padGL_apply`: the entries of the Library's `padGL h g`.
- `pad_mul`, `adelicEquiv_pad`, `continuous_pad`: the Library's `pad`
  is multiplicative, is `padGL` on matrices and is continuous.
- `isUnitriangular_padGL`, `pad_mem_unipotentAdelic`, `padUnipotent`:
  padding maps `N_m(𝔸)` into `N_n(𝔸)`.
- `sum_superdiag_padGL`, `genericCharacter_padUnipotent`: the generic
  character of `diag(n, I)` is that of `n`.

## Determinants

`detNorm_mul`, `detNorm_pos`, `continuous_detNorm`, `detNorm_rational`,
`detNorm_of_mem_rationalSubgroup`, `detNorm_unipotent`: the Library's
`detNorm` is a continuous positive homomorphism, trivial on rational
points and on `N_n(𝔸)`. `detPower_mul`, `detPower_add`,
`detPower_of_detNorm_eq_one`, `continuous_detPower`,
`detPower_rational_mul`, `detPower_unipotent_mul`: the corresponding
facts for `detPower`.

## Cusp forms and Whittaker functions

`mem_rationalSubgroup_of_unipotent`, `continuous_cuspFunction`,
`cuspFunction_rational_mul`: `cuspFunction F T v` is continuous and
left `GL(F)`-invariant. `cuspWhittaker_mul_left`:
`W(u g) = ψ_N(u) W(g)` for `u ∈ N_{r+1}(𝔸)` and a standard character
`ψ` (from `subgroupCharacterCoefficient_mul_left`).
`genericCharacter_rational_mul`, `measurable_cuspWhittaker`:
measurability of `cuspWhittaker`. `isStandardAdditiveCharacter_inv`:
`ψ⁻¹` is standard when `ψ` is.
