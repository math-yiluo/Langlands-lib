# The absolute norm of an idele

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormCore`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file defines the absolute norm on the idele group of a number field K, as a homomorphism to the units ℝ≥0ˣ, and the subgroup of ideles of norm one.

- `nnnormUnitHom F`: the norm on the units of a normed field F, as a unit of ℝ≥0.
- `InfiniteIdeleGroup.archimedeanNorm`: the product over the infinite places w of ‖a_w‖ raised to `w.mult`.
- `FiniteIdeleGroup.primeNorm`, `divisorNorm` and `FiniteIdeleGroup.absoluteNorm`: the finite part, ∏_v N(p_v)^(n_v). Here N(p_v) is the absolute norm of the prime and (n_v) is the exponent vector `valuationVector a`.
- `IdeleGroup.absoluteNorm`: the finite part times the inverse of the archimedean part.
- `IdeleGroup.normOneSubgroup`: the kernel of the absolute norm.

## Points to watch

- By the module comment, a uniformizer at v contributes N(p_v). This norm is therefore the reciprocal of the usual normalization ∏_v |a_v|_v. The kernel is the same under either convention.
- The module comment chooses this convention so that principal ideles have norm one, but this file does not prove that.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/NormCore.lean`: the Lean file is the source byte for byte (SHA-256 `bb3fd6ff502ad0a1dce348e47c485db2dbac2cda05e868918fcad50821f0e3b7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
