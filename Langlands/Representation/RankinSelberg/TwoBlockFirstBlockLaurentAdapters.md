# Adapters for the first-block Laurent assembly

Author: Worker 1037.

This module collects derived auxiliary facts for the first-block Laurent proof of
JPSS (1983), Section 4.9.

## Row character

`firstRowCharacter ψ n x` is the actual descent to `N \ GL_(n+1)` of
`v ↦ ψ((x v⁻¹)_0)`. It is well defined because right multiplication of a row by an
upper unipotent matrix does not change its first entry; this is the published
`TwoBlockLowerUnfolding.vecMul_upperUnipotent_zero`. The module proves:

- `firstRowCharacter_mk`, its representative formula;
- `norm_firstRowCharacter`, that it has norm one;
- `continuous_firstRowCharacter`, joint continuity on rows times the quotient, via
  the open quotient map;
- `aestronglyMeasurable_firstRowCharacter`, joint almost-everywhere strong
  measurability for every measure on that product, with the Borel quotient structure.

## Fiber maps

`aestronglyMeasurable_comp_fiberPoint_lowerRadical` proves joint almost-everywhere
strong measurability of `(Z, q) ↦ E([diag(v_q, 1) R(Z) g])` for every continuous
`E` on the upper block quotient. The proof composes the published continuity of the
fiber map with that of the lower radical.

## Degenerate cases

These lemmas give the vanishing of the actual integrands:

- `scalarSection_eq_zero_of_first`: every scalar section vanishes when the first
  functional is zero.
- `upperIntegrand_eq_zero_of_first` and `lowerIntegrand_eq_zero_of_first`: both
  published large integrands are therefore identically zero when the first
  functional is zero.
- `upperIntegrand_eq_zero_of_test` and `lowerIntegrand_eq_zero_of_test`: the same
  holds when the test function is zero.
- `coefficientModel_val_eq_zero`: every vector of the coefficient image of a zero
  test functional is the zero function.
