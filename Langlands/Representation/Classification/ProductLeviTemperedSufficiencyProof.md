# Proof of product-Levi tempered sufficiency from upper Jacquet exponents

Author: Worker 246.

This module proves the upper core statement
[`GLProductLeviTemperedExponentSufficiencyStatement`](ProductLeviTemperedSufficiencyStatement.md):

```text
theorem Langlands.glProductLeviTemperedExponentSufficiency :
    GLProductLeviTemperedExponentSufficiencyStatement.{uF, uV}
```

The field and representation universes `uF` and `uV` stay independent.
Auxiliary declarations are in the namespace `Langlands.ProductLeviTempered`. The
analytic estimate on the chamber is the published theorem
`Langlands.glProductLeviChamberCoefficientBound` of
[`ProductLeviChamberBoundProof`](ProductLeviChamberBoundProof.md). The count of
left cosets in a Cartan double coset is the published proposition
[`CartanQuotient.CartanCellCountStatement`](../../Group/GL/CartanCellCountStatement.md).
`tempered_of_cellCount` proves the target from that proposition. The final
theorem applies it to the published proof
`Langlands.GeneralLinear.CartanQuotient.cartanCellCount` of
[`CartanCellCountProof`](../../Group/GL/CartanCellCountProof.md).

## Integral subgroup and uniformizer

`discreteValuation_integer` identifies the integer ring of `T.discreteValuation`
with `T.Integers`. Hence `maximalCompact_eq`:
`CartanQuotient.maximalCompact T N` is
`Iwasawa.integralRange (ValuativeRel.valuation F.Carrier) N`. The product
`integralLevi T C` of these subgroups is the published compact open subgroup
`CuspidalSupport.LeviAdmissibility.integralLevi`. `isUniformizingElement` shows
that the specified uniformizer is a uniformizing element for
`T.discreteValuation`; its value is `exp (-1)`, and every nonzero value is an
integer power of it.

## Cells cover the central quotient

`exists_cell` applies the published Cartan decomposition
`GeneralLinear.Cartan.exists_cartan` in every block. It then subtracts the last
exponent, using `CartanQuotient.representative_shift`. The resulting family is
blockwise normalized, and the removed scalars form a central block scalar
(`blockScalarLevi_mem_center`). So every element of `Q = M_C / Z(M_C)` lies in
some cell

```text
cellQ lam = { mk (k₁ * leviRep lam * k₂) | k₁, k₂ ∈ integralLevi }.
```

Cells are indexed by `m : FundIndex C → ℕ` through
`latticeTuple m = ∑ s, m s • fundTuple s`. Every lattice tuple is blockwise
normalized (`latticeTuple_normalized`), and every normalized family arises as
`latticeTuple (fundCoeff lam)`. The index type is countable.

## Measures of cells

`measure_cellQ_le` uses the coset count in each block. The double coset of the
product is covered by the translates `r * a(lam) * integralLevi` with `r` in the
product finite set `Fintype.piFinset R`. Its size is `∏ j, |R j|` and is at most
`∏ j, c_j * delta(lam_j)⁻¹`. Every Haar measure is left invariant
(`measure_preimage_mul`). Hence

```text
μ (cellQ lam) ≤ ofReal (∏ j, c_j * delta(lam_j)⁻¹) * μ (mk '' integralLevi),
```

and the last factor is finite because the image is compact
(`measure_image_integralLevi_lt_top`). The cells need not be measurable;
outer measure is used throughout.

## Coefficients on cells

`cell_coefficient_bound` makes the chamber bound uniform on the cells. The
orbits of `v` and of the smooth functional `ℓ` under the compact open subgroup
`integralLevi` are finite (`Compact.finite_orbit_of_smooth` for `ρ` and for the
smooth contragredient). Also
`ℓ(ρ(k₁ a k₂) v) = (k₁⁻¹ · ℓ)(ρ(a)(ρ(k₂) v))`. So the constant is the finite sum
of the absolute values of the chamber constants over pairs of orbit elements.

## The `L^(2+ε)` estimate

The unitary central character is the published
`unitaryCentralCharacterOfBlockScalar`, built from the prescribed scalar
character `ω`. The carrier is nonzero because the representation is irreducible.
For `ε > 0` take `η = ε / (4 (2 + ε))`, `P = 2 + ε`, the fundamental weights
`w_s ∈ (0, 1)` and `y_s = w_s^(1/2 - η)`. On the cell of `m`, the coefficient
norm is at most `|c| * ∏ s, y_s ^ m s` (`prod_delta_latticeTuple`). The
`P`-th power of this bound, times the cell measure, is at most a constant times
`∏ s, x_s ^ m s` with `x_s = y_s^P * w_s⁻¹ = w_s^(ε/4) < 1`. The published
`finiteNatLatticeENNRealSummability` (with exponent `0`) shows that these terms
have finite sum over `FundIndex C → ℕ`. The published `countableCellLpUpper`
then gives `MemLp`, where almost-everywhere strong measurability comes from
`UnitaryCentralCharacter.aestronglyMeasurable_coefficientNorm`. Admissibility
is a hypothesis of the statement.
