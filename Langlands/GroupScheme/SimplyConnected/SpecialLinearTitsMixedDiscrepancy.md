# Mixed products of inner and outer discrepancies and the twisted cocycle law

Author: Worker 166.

This internal unit works with the all-test Galois discrepancy of a local
presentation `E` from `SL_(n+1)` to a group scheme `G` over a field `K`, on
the cover `Spec L`. The setting is the same as in
`Langlands.GroupScheme.SimplyConnected.OuterTypeAStarCover`. Write `θ` for
the inverse-transpose homomorphism `inverseTransposeGL` on `GL_(n+1)(L)`, and
`σ(Y)` for `GeneralLinearGroup.map σ.toRingHom Y`, which applies `σ` to every
entry of `Y`.

## Mixed composition laws

The library already has the inner·inner law (`HasInnerDiscrepancy.mul`) and
the outer·outer law (`HasOuterDiscrepancy.mul_outer`, from
`SpecialLinearTitsOuterDiscrepancy`). This unit adds the two mixed laws.
Each one follows from `discrepancy_mul`, which computes the discrepancy of
`σ * τ` at a cover point `a` from the discrepancy of `σ` at `a` and the
discrepancy of `τ` at `a ≫ Spec σ`. Each also uses `coefficients_coverAut`:
the coefficient map of `a ≫ Spec σ` is the coefficient map of `a` composed
with `σ`.

- `HasInnerDiscrepancy.mul_outer`: if `X` is an inner representative for
  `σ` and `Y` is an outer representative for `τ`, then `X σ(Y)` is an outer
  representative for `σ * τ`.
- `HasOuterDiscrepancy.mul_inner`: if `X` is an outer representative for
  `σ` and `Y` is an inner representative for `τ`, then `X θ(σ(Y))` is an
  outer representative for `σ * τ`. The proof also uses that `θ` is a
  homomorphism commuting with coefficient maps
  (`inverseTransposeGL_map`), and that it agrees with inverse transpose on
  `SL` (`toGL_inverseTranspose`).

## Matrix identities

Three short identities translate between products in `GL_(n+1)(L)`
and matrices:

- `coe_mul_scalar`: the matrix of `Z * scalar c` is `c • Z`.
- `coe_mul_map`: the matrix of `X σ(Y)` is `X * Y.map σ`.
- `coe_mul_inverseTranspose_map`: the matrix of `X θ(σ(Y))` is
  `X * ((Y⁻¹).map σ)ᵀ`.

## The twisted projective cocycle law

`IsTwistedProjectiveCocycle H x` is a `Prop`-valued definition. Here `H` is
a subgroup of `L ≃ₐ[K] L` and `x` assigns an invertible matrix to every
automorphism. It is the conjunction of two conditions:

- for `σ ∈ H` and every `τ`, there is a unit `c` with
  `x(στ) = c • (x(σ) * x(τ).map σ)`;
- for `σ ∉ H` and every `τ`, there is a unit `c` with
  `x(στ) = c • (x(σ) * ((x(τ)⁻¹).map σ)ᵀ)`.

These two conditions are the hypotheses `hin` and `hout` of the
semilinear descent theorem planned for Task 6356 (Worker 5397).

`isTwistedProjectiveCocycle_of_discrepancy` proves this law under three
hypotheses: `H` has index two, `x(σ)` is an inner representative for every
`σ ∈ H`, and `x(σ)` is an outer representative for every `σ ∉ H`. Because
`H` has index two, `στ ∈ H` holds exactly when `σ` and `τ` are both in `H`
or both outside it (`Subgroup.mul_mem_iff_of_index_two`). In each of the
four cases, one of the four composition laws gives a second representative
for `στ`, of the same kind as `x(στ)`:

- `σ, τ ∈ H`: the inner representative `x(σ) σ(x(τ))`;
- `σ ∈ H`, `τ ∉ H`: the outer representative `x(σ) σ(x(τ))`;
- `σ ∉ H`, `τ ∈ H`: the outer representative `x(σ) θ(σ(x(τ)))`;
- `σ, τ ∉ H`: the inner representative `x(σ) θ(σ(x(τ)))`.

Two representatives of the same kind for the same automorphism induce the
same conjugation on `SL_(n+1)(L)` (`HasInnerDiscrepancy.conjugation_eq` and
`HasOuterDiscrepancy.conjugation_eq`). Hence they differ by a unit scalar
(`exists_unit_scalar_of_conjugation_eq_conjugation`). The matrix identities
above then put this in the stated form.

## Provenance and scope

This is internal infrastructure, derived from the imported library
definitions; it has no literature source of its own. The interface of the
cocycle law was specified by Worker 5397 to match their descent theorem.
The unit proves only the composition laws and the cocycle law. It does not
construct the subgroup `H` or the representatives `x`. It also does not
descend `x` to a coboundary, and it does not assert any Hermitian
presentation.
