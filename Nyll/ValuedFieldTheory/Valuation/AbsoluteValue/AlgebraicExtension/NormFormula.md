# Algebraic properties of the norm formula for absolute values

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite field extension and `v` a real-valued absolute value on `K`. The library's candidate extension is `finiteExtensionNormFormulaValue v x = v(N(x))^(1/[L:K])`, with `N` the field norm from `L` to `K`. This file proves the algebraic properties of this function. Completeness and henselianity play no role. A last lemma concerns restricting valuations in a tower.

## Results on the norm formula

- `normFormula_finiteExtensionNormFormulaValue_eq_minpoly_coeff_zero_rpow`: the value at `x` is `v(a₀)^(1/d)`, where `a₀` is the constant coefficient and `d` the degree of the minimal polynomial of `x` over `K`. This is the same expression as for the spectral norm.
- `normFormula_finiteExtensionNormFormulaValue_algebraMap`: on elements of `K` the formula gives back `v`.
- `normFormula_finiteExtensionNormFormulaValue_pow_finrank_eq_norm`: the `[L:K]`-th power of the value is `v(N(x))`.
- `_eq_zero_iff`, `_mul`, `_inv` and `_div`: the value vanishes only at `0`, and it is multiplicative and compatible with inverses and quotients.
- `normFormula_finiteExtensionNormFormulaValue_le_one_iff_minpoly_coeff_zero_le_one`: the value is at most `1` exactly when `v(a₀) ≤ 1`.
- `normFormula_finiteExtensionNormFormulaValue_le_one_of_isIntegral`: let `v` be nonarchimedean in the sense of the library's `LubinTate.Valuations.NonarchimedeanAbsoluteValue`. If `x` is integral over the valuation ring `absoluteValueValuationSubring v` of elements with `v ≤ 1`, then the value at `x` is at most `1`.

The first formula combines two facts: the norm of `x` is `±a₀^[L:K(x)]`, and `[L:K] = d · [L:K(x)]`. The integrality statement uses that a valuation ring is integrally closed. Hence the minimal polynomial of `x` over `K` has coefficients in the valuation ring.

## Valuations in a tower

- `DiscreteValuationField.Valuation.comap_to_middle_hasExtension_of_top_hasExtension`: in a tower `K ⊆ L ⊆ M`, let `vM` be a valuation on `M` that extends `vK` on `K` (Mathlib's `Valuation.HasExtension`). Then the restriction of `vM` to `L` also extends `vK`.

## Points to watch

- The file does not prove the triangle inequality for the norm formula, so it does not show that the formula is an absolute value.
- The tower lemma holds for arbitrary valuations with values in linearly ordered commutative groups with zero, despite its namespace.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/AlgebraicExtension/NormFormula.lean`: the Lean file is the source byte for byte (SHA-256 `8ad7ea7183ff7c5f68875fe8744be4b45461321f592dde49dec51045c30dbd2c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
