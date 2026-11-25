# The norm formula is an absolute value over a henselian base

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite extension and `v` a nonarchimedean absolute value on `K` whose valuation ring `𝒪_v` satisfies a factorization form of Hensel's lemma. This file shows that `x ↦ v(N(x))^(1/[L:K])`, with `N` the field norm from `L` to `K`, is then a nonarchimedean absolute value on `L` extending `v`. Its valuation ring is the integral closure of `𝒪_v` in `L`.

## Main results

All results take three hypotheses:
- `hnonarch : NonarchimedeanAbsoluteValue v`, the library's predicate from the `LubinTate.Valuations` namespace;
- `hv : HenselFactorizationProperty (absoluteValueValuationSubring v hnonarch)`;
- `L/K` finite-dimensional.

- `normFormula_finiteExtensionNormFormulaValue_add_le_one_of_le_one_of_henselFactorization`: the set where the formula is at most `1` is closed under addition.
- `normFormula_finiteExtensionNormFormulaValue_strong_triangle_of_henselFactorization`: the value at `x + y` is at most the maximum of the values at `x` and `y`.
- `normFormula_finite_normFormulaAbsoluteValue_of_henselFactorization`: the formula bundled as an absolute value on `L`. Further theorems give its values, its restriction to `v` on `K`, and its nonarchimedean property.
- `normFormula_finite_mem_valuationSubring_iff_isIntegral_of_henselFactorization`: `x` has value at most `1` exactly when `x` is integral over `𝒪_v`.
- `normFormula_finite_valuationSubring_eq_integralClosure_of_henselFactorization`: the valuation ring of the bundled absolute value equals the integral closure of `𝒪_v` in `L`, as subrings.

## Proofs

Under the factorization hypothesis, the imported integral-closure file shows that an element with value at most `1` is integral over `𝒪_v`. The converse holds without it. Since sums of integral elements are integral, the unit ball is closed under addition. The ultrametric inequality follows by writing `x + y = x(1 + y/x)` and using multiplicativity.

## Points to watch

- `HenselFactorizationProperty` is the library's own predicate. It plays the role of Hensel's lemma and is carried as a hypothesis. Completeness of `K` is never assumed, and the file does not derive the property from completeness.
- The file proves existence of this extension only. Uniqueness of the extension is not addressed here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/AlgebraicExtension/NormFormulaAbsoluteValue.lean`: the Lean file is the source byte for byte (SHA-256 `d4b31f54492e82ef16acc7b034dded38854fbaa4eb6825579c7fb109dfc7a75c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
