# The exponential valuation `−log |x|` of a nonarchimedean absolute value

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.ExponentialValuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library works with nonarchimedean absolute values, which are multiplicative, and with exponential valuations, which are additive and real-valued. This file gives the canonical passage from the first to the second, `v(x) = −log |x|`, and shows that it is compatible with the reverse construction and with extensions of fields.

## Definitions and results

- `absoluteValueExponentialValuation abv hnonarch`: for `abv` nonarchimedean in the sense of the library's `NonarchimedeanAbsoluteValue`, the exponential valuation with value `−log abv(x)` at `x ≠ 0` and `⊤` at `0`. `_apply_zero` and `_apply_ne_zero` give these values. The inequality `v(x + y) ≥ min(v(x), v(y))` comes from the strong triangle inequality.
- `absoluteValueExponentialValuation_associated`: `abv` is associated to this valuation with base `e`, that is `abv(x) = e^(−v(x))` for `x ≠ 0` (`AssociatedAbsoluteValue`).
- `exponentialValuation_ext`: two exponential valuations with the same values are equal.
- `absoluteValueExponentialValuation_associated_eq`: start from an exponential valuation `v`, form the absolute value `exp(−v)` (`exponentialAssociatedAbsoluteValue`), and take `−log` again. The result is `v` itself, as an equality of structures.
- `absoluteValueExponentialValuation_extends`: if `aw` on `L` restricts exactly to `av` on `K`, both nonarchimedean, then the associated exponential valuations satisfy the same exact restriction.

## Points to watch

- `ExponentialValuation`, `AssociatedAbsoluteValue` and `NonarchimedeanAbsoluteValue` are the library's own notions from the `LubinTate.Valuations` namespace, not Mathlib's `Valuation` or `AddValuation`.
- The normalization is fixed: natural logarithm, base `e`. Other normalizations of the same valuation are not covered.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/ExponentialValuation.lean`: the Lean file is the source byte for byte (SHA-256 `16f5082849c31095c042f85a355b841b2addf322e930d02fff25a9dc01a6fab4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
