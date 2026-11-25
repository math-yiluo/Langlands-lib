# The integral closure of a henselian valuation ring is a valuation ring

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaIntegralClosure`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `v` be a nonarchimedean absolute value on a field `K` whose valuation ring `𝒪_v` satisfies the factorization form of Hensel's lemma. The file shows that in every algebraic extension `L/K`, each element or its inverse is integral over `𝒪_v`. So the integral closure of `𝒪_v` in `L` satisfies the defining property of a valuation ring.

## Main results

All results assume that `v` is nonarchimedean (the library's `NonarchimedeanAbsoluteValue`) and that `𝒪_v` satisfies `HenselFactorizationProperty`.

- `normFormula_finiteExtensionNormFormulaValue_isIntegral_of_le_one_of_henselFactorization`: for `L/K` finite, if `v(N(x))^(1/[L:K]) ≤ 1`, with `N` the field norm from `L` to `K`, then `x` is integral over `𝒪_v`.
- `normFormula_finite_integralClosure_mem_or_inv_of_henselFactorization`: for `L/K` finite, every `x ∈ L` or its inverse lies in the integral closure of `𝒪_v` in `L`.
- `normFormula_algebraic_integralClosure_mem_or_inv_of_henselFactorization`: the same for `L/K` algebraic.

## Proofs

If the norm-formula value of `x` is at most `1`, then so is the value of the constant coefficient of the minimal polynomial of `x`. The coefficient bound for monic irreducible polynomials, from the coefficients file, then puts all coefficients in `𝒪_v`. So the minimal polynomial is a monic polynomial over `𝒪_v` with `x` as a root. If the value is greater than `1`, the same argument applies to `x⁻¹`. The algebraic case is reduced to the finite extension `K(x)`.

## Points to watch

The henselian hypothesis is the library's own `HenselFactorizationProperty`, standing for Hensel's lemma. Neither completeness nor separatedness is assumed. The file does not build a `ValuationSubring` from the integral closure; it proves only the membership dichotomy.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/AlgebraicExtension/NormFormulaIntegralClosure.lean`: the Lean file is the source byte for byte (SHA-256 `3e680a7dc4c432a246d2a3d611522f1a6ed7b08d938cfdfa6810f3cd9605b243`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
