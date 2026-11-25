# Lifting coprime monic factorizations over a Henselian pair

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.CoprimeFactorLifting`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `R` be a commutative ring and `I` a maximal ideal along which `R` is Henselian (Mathlib's `HenselianRing`).

`exists_coprime_factor_lift`: if `f` is monic over `R` and its reduction modulo `I` factors as `ḡ · h̄` with `ḡ`, `h̄` monic and coprime over `R ⧸ I`, then there are monic, coprime `g`, `h` over `R` with `f = g · h`, `deg g = deg ḡ`, `deg h = deg h̄`, reducing to `ḡ` and `h̄`.

## Proof

The residual factorization is a point over `R ⧸ I` of Mathlib's universal coprime factorization algebra of `f`. This algebra is étale over `R`, so the point lifts to an `R`-point by the étale lifting result of an imported file; the universal factors at that point give `g` and `h`.

## Caveats

The ideal `I` is assumed maximal, and all polynomials involved are monic; the statement does not cover primitive, non-monic polynomials.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/CoprimeFactorLifting.lean`: the Lean file is the source byte for byte (SHA-256 `bc785e2e1385efb368c5de081e26021ac6d5086ff8fd679be4bcba638238dcca`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
