# Extending a complete nonarchimedean absolute value by the spectral norm

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.SpectralExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `v` be a nontrivial nonarchimedean real absolute value on a field `K`, complete in the sense that `WithAbs v` is a complete space, and let `L` be an algebraic extension of `K`. The file packages Mathlib's spectral norm of `L` over `WithAbs v` as an absolute value on `L` and shows it is the unique absolute value on `L` extending `v`.

## Main definitions and results

- `spectral_withAbsNontriviallyNormedField`: the nontrivially normed field structure on `WithAbs v` coming from `v.IsNontrivial`.
- `withAbsAlgebra_isAlgebraic`: `L` stays algebraic over `WithAbs v`.
- `spectral_spectralNorm_eq_zero_iff`: the spectral norm vanishes only at `0` (only algebraicity needed).
- `spectral_spectralNorm_mul`: the spectral norm is multiplicative, under completeness, nonarchimedeanity and nontriviality.
- `spectralExtension v hcomplete hnonarch hv : AbsoluteValue L ℝ`: the spectral norm as an absolute value.
- `spectralExtension_isNonarchimedean` and `spectralExtension_extends`: it satisfies the strong triangle inequality and restricts to `v` on `K` (the library's `Extends v w`).
- `eq_spectralExtension_of_extends`: every absolute value `w` on `L` with `Extends v w` equals `spectralExtension`.

## Proof

All properties are transferred from Mathlib's theory of the spectral norm (`spectralNorm_extends`, `isNonarchimedean_spectralNorm`, `spectralAlgNorm_mul`, `spectralNorm_unique_field_norm_ext`) after equipping `WithAbs v` with the needed instances (nontrivially normed field, ultrametric, complete).

## Points to watch

- The uniqueness statement does not assume that `w` is nonarchimedean; it holds for any absolute value on `L` restricting to `v`.
- `L` may be an infinite algebraic extension; no finiteness is assumed.
- The extension is defined through `WithAbs v` rather than on `K` directly; the base field's norm is `v` read through the `WithAbs` equivalence.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/SpectralExtension.lean`: the Lean file is the source byte for byte (SHA-256 `4cc0e1077444b9aee5fe3bcbf8d5a5cc5f1e5f04644dfa580cfd7841870644ed`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
