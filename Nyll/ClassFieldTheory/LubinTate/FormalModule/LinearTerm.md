# Prescribed linear terms of multivariable power series

Module `Nyll.ClassFieldTheory.LubinTate.FormalModule.LinearTerm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Over a commutative ring R, with finitely many variables Xᵢ indexed by σ, a multivariable power series H has prescribed linear term L : σ → R when H − Σᵢ Lᵢ·Xᵢ has total order at least 2. This is how the Lubin–Tate files state that a series begins with a given linear part.

## Main definitions

In `LubinTate.SameUniformizer`:

- `linearForm L`: the linear form Σᵢ Lᵢ·Xᵢ.
- `HasLinearTerm H L`: the proposition 2 ≤ order of H − `linearForm L`.

## Main results

- `constantCoeff_linearForm`: the linear form has zero constant coefficient.
- `HasLinearTerm.constantCoeff_eq_zero`: a series with prescribed linear term has zero constant coefficient.
- `HasLinearTerm.hasSubst`: such a series can be substituted into a one-variable power series.

## Watch for

- The order is Mathlib's total order of a multivariable power series, so the condition says that H has no constant term and that its coefficients of total degree 1 are the Lᵢ.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean`: the Lean file is the source byte for byte (SHA-256 `2c0d6016d13da48198c31b30bb92a21f054b6b74bc7d86a7c89076c3da8a391c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
