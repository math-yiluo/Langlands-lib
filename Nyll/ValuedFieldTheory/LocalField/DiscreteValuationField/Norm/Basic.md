# Integer-valued valuations on groups and valued norms

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Basic`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file works with an abstract group `G` (in applications, something like `Kˣ`) carrying a homomorphism to `ℤ`, and develops the elementary group theory behind "unit times power of a uniformizer": the kernel plays the role of the unit group `O_Kˣ`, and the quotient by it is the value group. At the end it defines a norm map compatible with two such valuations.

## Main definitions and results

- `MultiplicativeIntegerValuation G`: a function `val : G → ℤ` with `val 1 = 0` and `val (x * y) = val x + val y`; `valuationHom` is the same map as `G →* Multiplicative ℤ`. Formulas for inverses, quotients and integer powers follow, and elements of finite order have valuation `0`.
- `zeroSubgroup` (elements of valuation `0`, a normal subgroup equal to the kernel) and `valueSubgroup` (the range). `quotientZeroSubgroupEquivValueSubgroup : G ⧸ zeroSubgroup ≃* valueSubgroup`; if `val` is surjective, `quotientZeroSubgroupEquivMultiplicativeInt` identifies the quotient with `ℤ`. Membership of the image in `integerMultipleSubgroup d` is equivalent to `d ∣ val x`.
- `IsUniformizer ϖ` means `val ϖ = 1`; `hasUniformizer_iff_val_surjective`.
- `UnitUniformizerDecomposition ϖ x`: data `x = u * ϖ^n` with `val u = 0`. For a uniformizer, `canonicalUnitUniformizerDecomposition` takes `n = val x`, and the exponent and unit part are unique (`exponent_unique`, `unitPart_unique`, `unit_uniformizer_normal_form_eq_iff`).
- Many coset lemmas: `x / y` (or `y⁻¹ * x`) has valuation `0` iff `val x = val y` iff `x = u * y` (or `y * u`) with `val u = 0`; equality in `G ⧸ zeroSubgroup` is equality of valuations.
- `ValuedNorm vG vH`: a homomorphism `N : H →* G` with a natural number `residueDegree` such that `vG (N x) = residueDegree · vH x`.

## Points to watch

- `MultiplicativeIntegerValuation` is the library's own notion: a group homomorphism to `ℤ`, not a Mathlib `Valuation` on a ring. There is no zero element and no ultrametric inequality.
- In `ValuedNorm`, `residueDegree` is data certified only by the valuation formula, not defined as an invariant of a field extension, and `N` need not be a field norm.
- The module docstring speaks of norm-subgroup lemmas, but the file only defines `ValuedNorm` and proves nothing about it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Norm/Basic.lean`: the Lean file is the source byte for byte (SHA-256 `ebea2fe823fa7bf1a3adc9395af8645ebbad37531176e3f1165b1a6fed90a27e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
