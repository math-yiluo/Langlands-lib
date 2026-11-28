# Values of the `(1, n)` open-cell integrand

Module `Langlands.Representation.Shahidi.OpenCellBaseValues`, namespace
`Langlands.Shahidi.OpenCell.Base`.

## Contents

For `Ψ` right invariant under `GL_(t+1)(𝒪)`:
- `baseIntegrand_eq_zero_of_depth_ne`: the integrand is supported on the vectors of depth `d`;
- `baseIntegrand_isLatticePeriodic`, `integrable_baseIntegrand`: if moreover `ψ` has conductor
  `𝒪`, the integrand is lattice-periodic and integrable.

For `Ψ` of Whittaker type on `GL_(t+2)(K)`:
- `baseIntegrand_joinColumn_of_mem`: if `ψ` has conductor `𝒪` and `c` is integral, the integrand
  at the column `(y, c)` is `[d = 0 and y integral] Ψ(1)`.
- `twistOne`, `isWhittakerType_twistOne`, `baseIntegrand_joinColumn_of_valuation`: for
  `|c| = q^e` (`e ≥ 0`) and `z = c⁻¹ y`, the integrand at the column `(y, c)` is
  `conj ψ(c) ψ(z_last)` times the lift of `shellΦ (d - e) (twistOne ϖ Ψ e)` evaluated at
  `lower(z)`.
- `conj_char_neg`, `liftFunction_shellΦ_lower_neg`, `integral_char_mul_liftFunction`: for `Ψ`
  right invariant under `GL_(t+1)(𝒪)`, the substitution `z ↦ -z` turns `∫ ψ(z_last) F(lower z) dz` into the integral of the
  smaller-rank integrand `F(lower z) conj ψ(z_last)` (here `F` is the lift of a shell function).

## Provenance

Derived from `Langlands.Representation.Shahidi.OpenCellBaseLift`.
